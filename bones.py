# Vinnie's D&D Bones Game
# v1.2+

# coded by Christian Stober
# 10/2014 - 12/2014

###############################################################################
### CHANGE LOG
###############################################################################

# v1   first fully functional release
# v1.1 streamlined network interfaces to be more scalable, extensible, and
#      reusable
# v1.2 collapsed contents into single file

###############################################################################
### TODO LIST
###############################################################################

# when client receives / orates mid-sentence of typing, the new prompt still believes that text has been typed
# move helpers out of table formatting?
# game.status description
# command descriptions
# repr/str fix?
# enhance SeedBank making change algorithm
# alternate wager architecture: everyone says their maximum wager
# what if someone disconnects while others are playing i.e. they rejected, how to not interrupt game
# potential for multiple servers? - conflict with IP address posting / reading
# resolve annoying confusion: seeds return values as seeds, but banks return values as a net integer
# use None for e.g. acceptstatus?
# constantify animate roll parameters

# resolve file access issues (e.g. images) based on where script is run (for portability)
# safeguard against tight timing errors: e.g. two players wager simultaneously

###############################################################################
### NOTES
###############################################################################



###############################################################################
### MODULES
###############################################################################

import random
import cmd
import socket
import Queue
import threading
import time
import logging
import re
import urllib2
import errno
import traceback
import os
import sys
#from bones_gui import *

################################################################################
### CONSTANTS / PARAMETERS
################################################################################

########################################
# Die/scoring
########################################

# DIE              list of all possible outcomes when rolling a die (bone)
# DIE_COLOR_LUT    translation from symbol to name
# CODEBOOK         translates outcome of three rolls into a score (lower is better)
# FORFEITSCORE     worst score if you forfeit
# LONERSCORE       best score if you're the last man standing
# DIE_COLORS       list of colors on the die (bone)
# DIE_COLOR_NAMES  list of names of colors
DIE = ['R','R','R','B','B','G']
DIE_COLOR_LUT = {'R': 'Red', 'B': 'Blue', 'G': 'Green'}
CODEBOOK = {'GGG': 1, 'BGG': 2, 'BBB': 3, 'GGR': 4, 'BBG': 5, 'RRR': 6, 'GRR': 7, 'BBR': 8, 'BRR': 9, 'BGR': 10}
FORFEITSCORE = 11
LONERSCORE = 0

# derivations
DIE_COLORS = list(set(DIE)) # uniquify
DIE_COLOR_NAMES = [name for symbol, name in DIE_COLOR_LUT.iteritems()]

########################################
# Seed Colors / Values
########################################

# parameters for seed currency - all parameters derived from COLOR_CORE
# format: (symbol, name, value)
# one must have a value of one, set must be in ascending order of value, symbols must be unique
COLOR_CORE = [('y', 'yellow', 1), ('r', 'red', 10), ('b', 'blue', 100), ('g', 'green', 1000)]

### derivations - don't touch
# COLOR_LUT 		translates symbols into names
# COLOR_VAL_LUT 	translates symbols into values
# COLOR_VAL_INV 	translates values into symbols
# COLORS			list of color symbols sorted from least to greatest value
# COLOR_BASE		symbols of color with value of 1
# COLOR_VALS		list of values sorted from greatest to least
COLOR_LUT = {}
COLOR_VAL_LUT = {}
COLOR_VAL_INV = {}
for symbol, name, value in COLOR_CORE:
	COLOR_LUT[symbol] = name
	COLOR_VAL_LUT[symbol] = value
	COLOR_VAL_INV[value] = symbol
COLORS = [symbol for symbol, name, value in COLOR_CORE]
COLOR_BASE = COLOR_VAL_INV[1] # find the color that has a value of 1
COLOR_VALS = [value for symbol, name, value in COLOR_CORE]
COLOR_VALS.sort()
COLOR_VALS.reverse()

########################################
# Networking Parameters
########################################

# socket port the program
BONES_PORT = 821 # for Vinnie

# WWW_IP_URL - a web page that contains one IP address - that of the server as seen from the internet
# IPS_FNAME - a file that can be written to locally but accessed from a web page - currently accomplished with Dropbox
# IPS_URL - web page where the contents of IPS_FNAME can be accessed
WWW_IP_URL = "https://duckduckgo.com/?q=what+is+my+ip+address&t=keywordsearch"
IPS_FNAME = r"C:\Users\stoberc\Dropbox\bones\bonesip.txt"
IPS_URL = "https://www.dropbox.com/s/mto8psfi5zjb6kg/bonesip.txt?dl=1"

MAX_CLIENTS = 5 # max concurrent connection attempts to server

SERVER_LOGGING_LEVEL = logging.INFO
CLIENT_LOGGING_LEVEL = logging.WARNING
LOGGING_FORMAT = '%(asctime)s %(levelname)s: %(message)s'
LOGGING_DATE_FORMAT = '%H:%M:%S'
LOGFILE_DATE_FORMAT = '%Y-%m-%d ' + LOGGING_DATE_FORMAT
SERVER_LOGFILENAME = 'bones-server.log'

# time to wait between iterated client reconnection attempts measured in seconds
# padded to start counting from 1
RECONNECT_DELAYS = [0, 5, 20, 60]
MAX_RECONNECT_ITERATIONS = len(RECONNECT_DELAYS) - 1

# initial ID reserved for server
SERVERID = 0

########################################
# Command Parameters
########################################

### COMMANDS reference
# outdated - needs to be updated

### server to client ###

# assignID:5					# your id is assigned to e.g. 5
# newplayer:(pid,name) 			# there's a new player, id=1 name=Vinnie - broadcast
# nameadjust:(pid, name)		# player pid has changed her name to name
# accepts:id					# player pid has accepted the wager
# rejects:id					# player pid has rejected the wager
# message:%s					# transmit message to everyone
# wagerontable:(pid, wager)		# pid has offered wager
# accepts:pid					# pid accepts the wager
# rejects:pid					# pid rejects the wager
# round1:						# all parties have responded, we're moving to round1
# notakers:						# all parties have responded but no one accepted wager, back to forum
# orate:msg						# everyone display a message
# messagerelay:(pid, msg)		# pid says msg
# handrelay:(pid, hand)			# pid rolled hand
# response:						# all players have reported their hands, moving to response round

### client to server ###

# mynameis:%s					# notify client of name - triggers broadcast
# newname:Vinnie				# player has changed name
# wager:6y						# wager e.g. 6 yellows; appropriate during forum phase only
# accept:						# accept a wager on the table
# reject:						# reject a wager on the table
# message:msg					# please broadcast this message
# hand:hand						# my hand is ...


########################################
# Miscellaneous
########################################

DEFAULT_PLAYER_NAME = 'Anon'
CLI_PROMPT = '> '
TIGER_WORD = 'Ridat' # 'Ridat' or 'tiger'

RESPONSE_STATUS_LUT = {'c':'continue', 'f':'forfeit', 'd':'double'}
RESPONSE_STATUS_PAST_TENSE_LUT = {'c':'continued', 'f':'forfeited', 'd':'doubled'}

INTRO_ART = """
  ##################################
  ##                              ##
  ##  ####  #### #   # ####  ###  ##
  ##  #  ## #  # ##  # #    #     ##
  ##  ####  #  # # # # ###  ####  ##
  ##  #  ## #  # #  ## #       #  ##
  ##  ####  #### #   # #### ###   ##
  ##                              ##
  ##### by Vinnie and Christian ####
"""


################################################################################
### CLASSES
################################################################################

# an individual player
class Player:
	
	def __init__(self, name):
		self.name = name
		self.id = 0
		self.hand = [] # list of die rolls
		self.bank = SeedBank()
		self.acceptstatus = '' #a/r for accept/reject
		self.response = '' # response c/f/d for continue forfeit double
		self.rank = -1 # rank at end of game 1, 2, 3, etc.
		self.contribution = Seeds(0, COLOR_BASE) # amount put in pot
		self.income = Seeds(0, COLOR_BASE) # income from winning
		
	def __repr__(self):
		lines = []
		lines.append("Player name: " + self.name + "\n")
		lines.append("Player id: " + str(self.id) + "\n")
		lines.append("Player hand: " + self.gethand() + "\n")
		lines.append("Player acceptstatus: " + self.acceptstatus + "\n")
		lines.append("Player response: " + self.response + "\n")
		#lines.append(repr(self.bank))
		return ''.join(lines)
	
	def setid(self, id): self.id = id
	def getid(self): return self.id
	
	def setname(self, name): self.name = name
	def getname(self): return self.name
	
	def setrank(self, rank): self.rank = rank
	def getrank(self): return self.rank
	
	def getresponse(self): return self.response
	
	def setcontribution(self, contribution): self.contribution = contribution
	def getcontribution(self): return self.contribution
	def setincome(self, income): self.income = income
	def getincome(self): return self.income
	
	# find net income (your winnings - what you put in)
	# optimizes in the case of disparate colors
	def getnet(self):
		result = self.income - self.contribution
		if self.income.getcolor() != self.contribution.getcolor(): result.optimize()
		return result
	
	# roll a die and add it to the hand, return it for external use
	def roll(self):
		result = random.choice(DIE)
		self.hand.append(result)
		return result
	
	# number of rolls (excludes 'X' from forfeiture)
	def nrolls(self):
		return len(self.hand) - self.hand.count('X')
	
	# return the hand as a string e.g 'RG'
	def gethand(self): return ''.join(self.hand)
	
	# configure the hand using e.g. 'RBB'
	# used for filling in local data on other players from server
	def sethand(self, hand): self.hand = [roll for roll in hand]
	
	# reset back to forum following full or partial game (wagering onward)
	def reset(self):
		self.hand = []
		self.response = ''
		self.acceptstatus = ''
		self.rank = -1
		self.contribution = Seeds(0, COLOR_BASE)
		self.income = Seeds(0, COLOR_BASE)
		
	# score the three dice rolls
	# assume caller knows to only call at end of game - will throw exception else
	def getscore(self):
		if self.forfeited(): return FORFEITSCORE
		elif self.nrolls() == 2: return LONERSCORE
		handc = self.hand[:] # don't want to sort the original, do we?
		handc.sort()
		return CODEBOOK[''.join(handc)]
		
	def accept(self): self.acceptstatus = 'a'
	def reject(self): self.acceptstatus = 'r'
	def accepted(self):	return self.acceptstatus == 'a' # True/False
	def rejected(self):	return self.acceptstatus == 'r' # True/False
	def responded_to_wager(self): return self.accepted() or self.rejected() # True/False
	
	def continue_(self): self.response = 'c'
	def forfeit(self):
		# don't allow double forfeit due to server redundancy
		# normally inconsequential, but here would cause double 'X'
		if self.response == 'f': return
		self.response = 'f'
		self.hand += ['X']
	def double(self): self.response = 'd'
	def continued(self): return self.response == 'c'
	def forfeited(self): return self.response == 'f'
	def doubled(self): return self.response == 'd'
	def responded_to_cfd(self): return self.continued() or self.forfeited() or self.doubled()
	
	# fails if a person contributed 0 seeds
	# should be impossible if game mechanics are implemented correctly
	def contributed(self): return self.getcontribution() > Seeds(0, COLOR_BASE)

# class for currency - atomic units e.g. five yellows, three blues
class Seeds:
	
	def __init__(self, count, color):
		if not isinstance(count, int):
			raise Exception("Error: non-integer count input to Seeds - %s" % count)
		if color not in COLORS:
			raise Exception("Error: invalid color input into Seeds - %s. Try one of these:%s" % (color, ' '.join(COLORS)))
		self.count = count
		self.color = color
		
	# violates convention that __repr__ return value should be pythonic, but very convenient for debug
	def __repr__(self):
		if self.count == 1:
			suffix = ''
		else:
			suffix = 's'
		return "%d %s%s" % (self.count, COLOR_LUT[self.color], suffix)
		
	def __cmp__(self, other):
		return cmp(self.value(), other.value())

	# keeps color if both inputs are the same color
	def __add__(self, other):
		s = Seeds(self.value() + other.value(), COLOR_BASE)
		if self.getcolor() == other.getcolor():
			s.convert(self.getcolor())
		else:
			s.optimize()
		return s
	
	# if both arguments are same color, result will match
	def __sub__(self, other):
		s = Seeds(self.value() - other.value(), COLOR_BASE)
		if self.getcolor() == other.getcolor():
			s.convert(self.getcolor())
		else:
			s.optimize()
		return s
	
	def __mul__(self, n):
		count = n * self.getcount()
		return Seeds(count, self.getcolor())
		
	__rmul__ = __mul__
	
	# keeps same color when possible, else optimizes
	def __div__(self, n):
		value = int(self.value() / n)
		result = Seeds(value, COLOR_BASE)
		if value % COLOR_VAL_LUT[self.getcolor()] == 0:
			result.convert(self.getcolor())
		else:
			result.optimize()
		return result
	
	# keeps same color when possible, else optimizes
	def __mod__(self, n):
		value = int(self.value() % n)
		result = Seeds(value, COLOR_BASE)
		if value % COLOR_VAL_LUT[self.getcolor()] == 0:
			result.convert(self.getcolor())
		else:
			result.optimize()
		return result		
		
	def __divmod__(self, n): return (self/n, self%n)

	def getcolor(self): return self.color
	def getcount(self): return self.count
	def value(self):
		return self.count * COLOR_VAL_LUT[self.color]
		
	# converts into a different color
	# returns any incurred loss
	# e.g. convert 34 yellows into red converts into 3 reds, returning 4 yellows
	# if refuse_imperfect = True, the conversion will only succeed if there's no remainder
	def convert(self, color, refuse_imperfect = False):
		count, residual = divmod(self.value(), COLOR_VAL_LUT[color])
		if refuse_imperfect and residual != 0:
			return Seeds(0, COLOR_BASE)
		r = Seeds(residual, self.color)
		self.color = color
		self.count = count
		return r
		
	# convert to the highest denomination possible without loss
	def optimize(self):
		# cycle through them until the first viable match is found (could be self)
		# relies on COLOR_VALS being in descending order
		for value in COLOR_VALS:
			if self.value() % value == 0:
				self.convert(COLOR_VAL_INV[value])
				return		
		
# currency management - bank of varying quantities of each currency
class SeedBank:
	def __init__(self):
		self.bank = {}
		for color in COLORS:
			self.bank[color] = 0
	
	# violates convention that __repr__ return value should be pythonic, but very convenient for debug
	def __repr__(self):
		output = "Bank contents:\n"
		for color in COLORS:
			output += " " + str(Seeds(self.bank[color], color)) + "\n"
		totalvalue = Seeds(self.value(), COLOR_BASE)
		totalvalue.optimize()
		output += "Total value: %s\n" % totalvalue
		return output
	
	def __getitem__(self, key):
		return self.bank[key]
		
	def __setitem__(self, key, count):
		self.bank[key] = count
	
	# return a duplicate of the object
	def copy(self):
		c = SeedBank()
		c.bank = self.bank.copy()
		return c
		
	# find the total bank value
	# returns value as # of yellow seeds
	def value(self):
		total = 0
		for color in COLORS:
			total += self.bank[color] * COLOR_VAL_LUT[color]
		return total
	
	def deposit(self, seeds):
		self.bank[seeds.getcolor()] += seeds.getcount()
	
	# instead of deposit COULD do bank + seeds
	# perhaps better to stick with deposits, though for readability?
	def __add__(self, seeds):
		result = self.copy()
		result.deposit(seeds)
		return result
	
	# attempts to withdraw desired number of seeds
	# returns the balance that is actually withdrawn (could be different than request in the case of bankruptcy)
	def withdraw(self, seeds, settleforless = True):
		# try to withdraw that exact seed amount
		if self.bank[seeds.getcolor()] >= seeds.getcount():
			self.bank[seeds.getcolor()] -= seeds.getcount()
			return seeds
		
		# otherwise, withdraw equivalent amount - 
		# for now, just turn everything to yellows, then force optimization
		# can later implement more natural (but complex) algorithm:
		# starting with color requested, then break up larger denominations, 
		# then group smaller denominations
		elif self.value() >= seeds.value():
			target = seeds.value()
			bv = self.value()
			
			for color in COLORS:
				if color == COLOR_BASE:
					self.bank[color] = bv - target
				else:
					self.bank[color] = 0
				
			self.optimize()
			
			return seeds
					
		# withdraw max amount if willing to settle
		elif settleforless:
			bv = Seeds(self.value(), COLOR_BASE)
			bv.optimize()
			
			for color in COLORS:
				self.bank[color] = 0
			
			# if possible, return in the desired color
			if bv.getcount() % COLOR_VAL_LUT[seeds.getcolor()] == 0:
				bv.convert(seeds.getcolor())
	
			return bv
		
		# if unwilling to settle, then you don't get anything back
		else:
			return Seeds(0, COLOR_BASE)
									
	# rebalance bank to use highest valued seeds possible
	def optimize(self):
		remaining = self.value()
		
		for value in COLOR_VALS:
			color = COLOR_VAL_INV[value]
			count, remaining = divmod(remaining, value)
			self.bank[color] = count

# base class for server and client game management containing mutually necessary functions
# useless independently
class Game:
	
	def __init__(self):
		self.rankingsknown = False
		self.wager = Seeds(0, COLOR_BASE)
	
	def __str__(self):
		lines = []
		lines.append("Status: " + self.status + "\n")
		lines.append("N Players: " + str(self.nplayers()) + "\n\n")
		if self.localplayerid: lines.append("Local player:\n" + str(self.localplayer()) + "\n")
		lines.append("External players:\n\n")
		for playerid in self.players:
			if playerid == self.localplayerid: continue
			lines.append(str(self.players[playerid]) + "\n")
		return ''.join(lines)	
	
	def start(self):
		self.ni.start()
				
		if self.ui:
			self.ui.start()
		else:
			while True: time.sleep(1000)
	
	# most of the following are optimized for readability rather than performance, since performance is a non-issue
	
	# if we're back in the forum phase, reset all players
	def forumreset(self):
		self.status = 'forum'
		self.wager = Seeds(0, COLOR_BASE)
		for player in self.playerlist():
			player.reset()
		self.rankingsknown = False
	
	# set the wager for the game
	def setwager(self, wager):
		if not isinstance(wager, Seeds):
			print "\nNon-Seeds input to game.setwager: %s" % wager
		self.wager = wager
	def getwager(self):	return self.wager
	
	def netcontributions(self):
		contributions = [player.getcontribution() for player in self.accepted_players()]
		total = contributions[0]
		for c in contributions[1:]:
			total += c
		return total
		
	###############################################
	### COUNT PLAYERS WITH PARTICULAR CHACTERISTICS
	
	def nplayers(self):	return len(self.players)
	
	# number of player who've rolled n times (to our knowledge)
	def nrolled(self, n): return sum([player.nrolls() == n for player in self.playerlist()])
	
	def naccepted(self): return sum([player.accepted() for player in self.playerlist()])
	def nrejected(self): return sum([player.rejected() for player in self.playerlist()])
	def nrespondents(self):	return self.naccepted() + self.nrejected()
	
	def ncontinued(self): return sum([player.continued() for player in self.playerlist()])
	def nforfeited(self): return sum([player.forfeited() for player in self.playerlist()])
	def ndoubled(self): return sum([player.doubled() for player in self.playerlist()])
	# number of players who get to participate in round2 (responded continue or double)
	def nround2(self): return self.ncontinued() + self.ndoubled()
	
	# number who have continue/forfeit/double values assigned
	def ncfd(self): return self.ncontinued() + self.nforfeited() + self.ndoubled()
	
	def ncontributed(self): return sum([player.contributed() for player in self.playerlist()])
	
	def nwinners(self): return len(self.winners())
	
	####################################################
	### LISTS OF PLAYERS WITH PARTICULAR CHARACTERISTICS
	
	def playerlist(self): return [player for pid, player in self.players.iteritems()]
	def accepted_players(self): return [player for player in self.playerlist() if player.accepted()]
	def rejected_players(self): return [player for player in self.playerlist() if player.rejected()]
	def continued_players(self): return [player for player in playerlist() if player.continued()]
	def doubled_players(self): return [player for player in playerlist() if player.doubled()]
	def forfeited_players(self): return [player for player in playerlist() if player.forfeited()]
	def cfd_players(self): return [player for player in playerlist() if player.responded_to_cfd()]
	def round2_players(self): return [player for player in self.playerlist() if player.continued() or player.doubled()]
	
	# only works if rankings have been calculated, otherwise raises error
	def winners(self):
		if not self.rankingsknown:
			raise Exception("Trying to find winners/losers but calcrankings has not been run.")
		return [player for player in self.playerlist() if player.getrank() == 1]
	def losers(self):
		if not self.rankingsknown:
			raise Exception("Trying to find winners/losers but calcrankings has not been run.")
		return [player for player in self.playerlist() if player.getrank() != 1]
	
	# determines the ranking of scores and saves it for every player
	def calcrankings(self):
		accepted_players = self.accepted_players()
		scores = [player.getscore() for player in accepted_players]
		scores.sort()
		
		# make a LUT to convert scores into rankings (incl. ties) e.g.
		# [4, 4, 7, 11, 11, 11, 12] ->
		#  {4:1, 7:3, 11:4, 12:7}
		#  4 is 1st, 7 is 3rd, 11 is 4th, 12 is 7th
		ranking = {}
		i = 1
		for score in scores:
			if score not in ranking:
				ranking[score] = i
			i += 1
		# alternate algorithm: start with worst rank and fill in ranking unconditionally
		# ties will be naturally overridden instead of creating a new entry in dict
		#scores.reverse()
		#i = len(scores)
		#for score in scores: ranking[score]=i; i-=1
		
		for player in accepted_players:
			player.setrank(ranking[player.getscore()])
		
		self.rankingsknown = True

# client-side container for game data and management
class GameClient(Game):

	def __init__(self, useGUI = False):
		Game.__init__(self)
		player = Player(DEFAULT_PLAYER_NAME)
		self.localplayerid = player.getid()
		self.players = {player.getid(): player}
		self.ni = NetworkInterfaceClient(self)
		self.status = 'disconnected'
		
		# configure logger
		logging.basicConfig(level = CLIENT_LOGGING_LEVEL, format = LOGGING_FORMAT, datefmt = LOGGING_DATE_FORMAT)

		# configure user interface as CLI or GUI
		if useGUI: self.ui = GUI(self)
		else: self.ui = CLI(self)
		
	# accesses the local player
	def localplayer(self):
		if self.localplayerid is not None: # necessary language because id can be zero
			return self.players[self.localplayerid]

# server-side container for game data and management
class GameServer(Game):
	
	def __init__(self):
		Game.__init__(self)
		self.localplayerid = None
		self.players = {}
		self.ni = NetworkInterfaceServer(self)
		self.ui = None # no user interface to the server
		self.status = 'forum'
		
		# configure logger to file and to console
		logging.basicConfig(level = SERVER_LOGGING_LEVEL,
							filename = SERVER_LOGFILENAME,
							format = LOGGING_FORMAT,
							datefmt = LOGFILE_DATE_FORMAT)
		console = logging.StreamHandler()
		console.setLevel(SERVER_LOGGING_LEVEL)
		console.setFormatter(logging.Formatter(LOGGING_FORMAT, LOGGING_DATE_FORMAT))
		logging.getLogger().addHandler(console)
		
# common functionality for server and client network interfaces
class NetworkInterface:
	
	# background thread pulls tasks off the queue and processes them
	def queue_manager(self):
		while True:
			id, command, args = self.q.get()
			logging.debug("Q: id / command / args = %d / %s / %s " % (id, command, args))
			self.command_handler(id, command, args)

	# transmit a message to connection designated by id
	# caution to user: all args will be converted to string for transmission
	# receiver must process that data string
	# logging can be turned off, typically if part of a larger broadcast event
	def tx(self, command, args = '', id = SERVERID, log = True):
		
		if id not in self.connections:
			self.game.ui.msg("Error: attempting to transmit to unknown connection.")
			logging.info("Error: attempting to transmit to unknown connection %d." % id)
		
		args = str(args)
		arglength = len(args)
		packet = "%s:%d:%s|" % (command, arglength, args)
			
		# log the communication BEFORE tx in case an immediate response follows
		if log:
			ndigits_id = len(str(id))
			ndigits_maxid = len(str(max(self.connections)))
			padding = ndigits_maxid - ndigits_id
			logging.info(' ' * padding + 'Channel %d tx:  %s:%s' % (id, command, args))
	
		thread, sock, sockdetails = self.connections[id]
		sock.sendall(packet)
	
	# transmit a message to all active connections
	def broadcast(self, command, args = ''):
		# log the communication BEFORE tx in case of immediate response
		if len(self.connections) > 0:
			ndigits_maxid = len(str(max(self.connections)))
		else:
			ndigits_maxid = 1
		padding = ndigits_maxid - len('B')
		logging.info(' ' * padding + 'Channel B tx:  %s:%s' % (command,args))		
		
		for id in self.connections:
			self.tx(command, args, id, log = False)
			

	
	# run as thread to manage an individual connection rx line
	# parses incoming data and places commands onto task queue
	# packet structure is command:arglength:argstring|
	# e.g.: contribution:12:Seeds(5,'y')|
	# e.g.: forum:0:|
	# final pipe is a waste of space, but since network activity is fairly low, keep for readability of data stream
	def rx(self, id, sock):
		
		data = '' # empty buffer
		seekHeader = True # waiting for a packet header
		
		# forever try to receive and parse commands, placing them in the queue
		while True:
		
			# add new data to the buffer
			try:
				data += sock.recv(1024)
			except socket.error as error: # if the client has vanished...
				if error.errno == errno.WSAECONNRESET:
					self.broken_connection(id)
					return
				else:
					logging.exception("Indeterminate socket problem in rx.")
					raise
						
			# parse as many commands out of the data as possible until continuing to wait for more data
			while True:
				# waiting for a header
				if seekHeader:
					
					# try to find a command amongst the data
					header_re = '(.*?):(\d*):(.*)'
					x = re.search(header_re, data)
				
					# if no complete command has been found, break and wait for more data
					if x == None: break
					
					# parse the command
					command, arg_length, moredata = x.group(1), int(x.group(2)), x.group(3)
				
					# leave behind the excess data
					data = moredata
					
					seekHeader = False # look for data instead now

				# waiting for argument data
				if not seekHeader:
					
					# if there's insufficient data in the buffer, break and wait for more data
					if len(data) < arg_length + 1:
						break
				
					# extrace the necessary amount of data
					args = data[:arg_length]
					
					if data[arg_length] != '|':
						logging.error("Malformed packet in rx:")
						logging.error("  >%s:%s:%s" % (command, arg_length, data))
						raise Exception("Bad packet in rx")
					
					# keep the rest of the data
					data = data[arg_length + 1:]
					
					# log receipt BEFORE putting on Q in case of immediate follow up TX
					# assumption: maxid is changing relatively slowly
					# pad so that single and double digit channels are colon aligned
					ndigits_id = len(str(id))
					ndigits_maxid = len(str(max(self.connections)))
					padding = ndigits_maxid - ndigits_id
					logging.info(" " * padding + "Channel %d rx: %s:%s" % (id, command, args))

					# place the command etc. in the queue
					self.q.put((id, command, args))
										
					seekHeader = True

	# string to tuple safely for incoming command arguments
	def tuple_unpack(self, args): return eval(args, {'__builtins__':None})

# server network interface
class NetworkInterfaceServer(NetworkInterface):

	def __init__(self, game):
		self.game = game
	
	# starts the server
	def start(self):
	
		logging.info("Launching server...")
		
		# find and post ip addresses
		self.acquire_ips()
		self.post_ips()

		# create and start the connection hub thread
		self.hub_thread = threading.Thread(target = self.connection_hub, name = 'connection_hub')
		self.hub_thread.daemon = True # so that it will not attempt to persist when the program terminates
		self.hub_thread.start()
		
		# create connections dictionary
		# format of a connection is connectionID: (thread, socket, socketDetails)
		self.connections = {}
		
		# create the task queue
		self.q = Queue.Queue()
		
		# create and start the queue handler thread
		self.q_handler_thread = threading.Thread(target = self.queue_manager, name = 'q-manager')
		self.q_handler_thread.daemon = True # so that it will not attempt to persist when the program terminates
		self.q_handler_thread.start()
			
	# find the three ip addresses for this machine - localhost, the lan IP, and the www IP - in that order
	def acquire_ips(self):
		localhostip = '127.0.0.1'
		
		# lan ip
		s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
		try:
			s.connect(('duckduckgo.com', 0))
			lanip = s.getsockname()[0]
			s.close()
		except socket.gaierror: # no web access? localhost is our only chance
			lanip = ''
			wwwip = ''
			self.ips = [localhostip, lanip, wwwip]
			logging.warning("Unable to identify IP address on network.")
			logging.warning("Assuming machine is disconnected from the network.")
			logging.warning("Only a localhost game can proceed.")
			return
			
		# www ip
		try:
			webpagestring = urllib2.urlopen(WWW_IP_URL).read()
			ip_re = "Your IP address is (\d+\.\d+\.\d+\.\d+)"
			wwwip = re.search(ip_re, webpagestring).group(1)
		except urllib2.URLError:
			logging.warning("Unable to open the following URL for www IP acquisition.")
			logging.warning(WWW_IP_URL)
			logging.warning("Unable to host WWW game.")
			wwwip = ''
		except AttributeError:
			logging.warning("Unable to find IP address in contents of this page:")
			logging.warning(WWW_IP_URL)
			logging.warning("Unable to host WWW game.")
			wwwip = ''
		
		self.ips = [localhostip, lanip, wwwip]
		logging.info("IPs have been posted:")
		logging.info(self.ips)
		
	# post ips to web accessible file
	def post_ips(self):
		try:
			fp = open(IPS_FNAME,'w')
			fp.write('\n'.join(self.ips))
			fp.close()
		except IOError as e:
			if e.errno == 2: # no such file or directory
				logging.warning("Unable to write to IP file because directory is not found.")
				logging.warning("Path: %s" % IPS_FNAME)
	
	# listens indefinitely to establish incoming connections
	# runs as thread
	def connection_hub(self):
		
		# create a socket to receive incoming connections
		s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
		s.bind(('', BONES_PORT))
		s.listen(MAX_CLIENTS)
		logging.info("Connection hub activated...")
		
		# any time an incoming connection is received, assign it an id and start a dedicated thread to listen
		connectionID = 1 + SERVERID # start at 1 - 0 reserved for server
		while True:	
			
			# accept connections
			sock, sockdetails = s.accept()
			
			# start a thread to manage the new connection
			rx_thread = threading.Thread(target = self.rx, args = (connectionID, sock), name = 'server_rx')
			rx_thread.daemon = True # so that it will not attempt to persist when the program terminates
			rx_thread.start()
			
			# update the connections register
			self.connections[connectionID] = (rx_thread, sock, sockdetails)
			
			logging.info("New connection. Id / Host / Port = %d / %s / %d" % (connectionID, sockdetails[0], sockdetails[1]))
		
			connectionID += 1
		
	# USER DEFINED
	# The rest of the functions are user-defined
	# 1. broken_connection - how to respond to a broken connection
	# 2. command_handler - how to respond to received commands
	
	def broken_connection(self, id):
		# delete the player and connection
		del self.connections[id]
		del self.game.players[id]
					
		# then tell everyone the client has vanished
		# reset to forum, then kill this thread
		self.broadcast('mandown', id)
		self.broadcast('forum')
		self.game.forumreset()		
		
	def command_handler(self, id, command, args):
		try:
			handler = eval('self.cmd_%s' % command)
		except:
			logging.warning("Channel " + str(id) + " unrecognized rx command: " + str((command,args)))
			return
		handler(id, args)
	
	# a player is introducing themselves (immediately following connection)
	# assign them an ID and notify everyone about players
	def cmd_mynameis(self, id, args):
			
		# notify the new player of their player id
		self.tx('assignID', id, id)
	
		# for simplicity I broadcast EVERY player (so the newest player can hear about everyone)
		#  and count on the clients to ignore redundant info
		name = args
		newplayer = Player(name)
		newplayer.setid(id)
		self.game.players[id] = newplayer
		for playerid in self.game.players:
			player = self.game.players[playerid]
			self.broadcast('newplayer', (player.getid(), player.getname()))
								
		# if game is already under way, just pretend the current player rejected the wager
		if self.game.status != 'forum': self.game.players[id].reject()
			
		# tell them to wait if a game is already in progress
		if self.game.status != 'forum':
			self.tx('hold', '', id)
	
	# if someone announces a newname, broadcast the new name
	def cmd_newname(self, id, args):
		name = args
		self.game.players[id].setname(name)
		self.broadcast('nameadjust', (id, name))
			
	# a wager is made
	def cmd_wager(self, id, args):
		if self.game.status != 'forum': return
		
		# if you proposed the wager, you automatically accept it
		self.game.players[id].accept()
		
		value, color = self.tuple_unpack(args)
		self.game.wager = Seeds(value, color)
		
		self.game.status = 'wagering'
		self.broadcast('wagerontable', (id, value, color))
			
	# if someone accepts, log it and pass along the message to all
	# if this is the final response, move to the next phase
	def cmd_accept(self, id, args):
		if self.game.status != 'wagering': return
		self.game.players[id].accept()
		self.broadcast('accepts', id)
		self.acceptreject_helper() # act on final response
		
	# if someone rejects log it and pass along the message to all
	# if this is the final response, move to the next phase		
	def cmd_reject(self, id, args):
		if self.game.status != 'wagering': return
		self.game.players[id].reject()
		self.broadcast('rejects', id)
		self.acceptreject_helper() # act on final response
		
	# if someone sends a message, just relay to all
	def cmd_message(self, id, args):
		msg = args
		outargs = str((id, msg))
		self.broadcast("messagerelay", outargs)

	# if someone sends a hand, log it, relay it, and if it's the last one we're waiting for, move on
	def cmd_hand(self, id, args):
		if self.game.status not in ['round1', 'round2']: return
		hand = args
		self.game.players[id].sethand(hand)
		outargs = str((id, hand))
		self.broadcast("handrelay", outargs)
		
		# Round 1:
		# if this was the last person we're waiting to hear from, then move to response round
		if self.game.status == 'round1' and self.game.nrolled(2) == self.game.naccepted():
			self.game.status = 'response'
			self.broadcast("response")
		
		# Round 2
		# if this was the last person we're waiting to hear from, move to denouement
		if self.game.status == 'round2' and self.game.nrolled(3) == self.game.nround2():
			self.game.status = 'denouement'
			self.broadcast("denouement")
	
	# the client has chosen to continue
	def cmd_continue(self, id, args):
		if self.game.status != 'response': return
		self.game.players[id].continue_()
		self.cfd_helper() # act on final response
		
	# the client has chosen to forfeit
	def cmd_forfeit(self, id, args):
		if self.game.status != 'response': return
		self.game.players[id].forfeit()
		self.cfd_helper() # act on final response
		
	# the client has chosen to double
	def cmd_double(self, id, args):
		if self.game.status != 'response': return
		self.game.players[id].double()
		self.cfd_helper() # act on final response
		
	# a player submits their contribution
	# may be different than their debt in case of lots of doubling
	# can't just relay because ties require arbitration for unequal division of winnings
	def cmd_contribution(self, id, args):
		value, color = self.tuple_unpack(args)
		self.game.players[id].setcontribution(Seeds(value, color))
		
		# let all clients know about this contribution
		# (so they can calculate net earnings later)
		cr_msg = str((id, value, color))
		self.broadcast('contributionrelay', cr_msg)
		
		# if all contributions have been reported, calculate final distribution
		if self.game.ncontributed() == self.game.naccepted():
			pot = self.game.netcontributions()
			self.game.calcrankings()
			
			winnerids = [player.getid() for player in self.game.winners()]
			loserids = [player.getid() for player in self.game.losers()]
			nwinners = self.game.nwinners()
			
			# easy if there's just one winner
			if nwinners == 1:
				winnerid = winnerids[0]
				msg1 = ((winnerid, pot.getcount(), pot.getcolor()),)
			
			# if pot can be divided evenly, do it
			elif pot % nwinners == Seeds(0, COLOR_BASE):
				share = pot / nwinners
				msg1 = tuple([(id, share.getcount(), share.getcolor()) for id in winnerids])
			
			# otherwise, randomly distribute the excess
			else:
				lowshare, residue = divmod(pot, nwinners)
				highshare = lowshare + Seeds(1, COLOR_BASE)
				lowshare.optimize()
				highshare.optimize()
				nhigh = residue.value()
				winnerids.shuffle()
				highids = winnerids[:nhigh]
				lowids = winnerids[night:]
				highlist = [(id, highshare.getcount(), highshare.getcolor()) for id in highids]
				lowlist = [(id, lowshare.getcount(), lowshare.getcolor()) for id in lowids]
				msg1 = tuple(highlist + lowlist)
			
			msg2 = tuple([(id, 0, pot.getcolor()) for id in loserids])
			
			msg = msg1 + msg2
			msg = str(msg) # to offset faulty feature of single element tuple string interpolation
			self.broadcast('spoils', msg)
			self.broadcast('forum')
			
			self.game.status = 'forum'
			self.game.forumreset()
						
	# check / act on final response to accept/reject
	def acceptreject_helper(self):
		if self.game.nrespondents() == self.game.nplayers():
			if self.game.naccepted() >= 2:
				self.game.status = 'round1'
				self.nrespondents = 0
				self.broadcast("round1")
			else:
				self.game.status = 'forum'
				self.game.wager = Seeds(0, COLOR_BASE)
				self.broadcast("forum")
				self.game.forumreset()
			
	# after a continue/forfeit/double checks if everyone has responded
	# if so, decides appropriate subsequent transmissions
	# should this be in scope of queue_manager() only?
	def cfd_helper(self):
		if self.game.ncfd() == self.game.naccepted():
			responses = str(tuple([(player.getid(), player.getresponse()) for player in self.game.accepted_players()]))
			# e.g. ((1,'d'), (2, 'f'), (3,'c'))
			self.broadcast('responses', responses)		
			
			# if at least two players are still standing, move to round 2
			# otherwise, game over (default or no contest)
			if self.game.nround2() >= 2:
				self.game.status = 'round2'
			elif self.game.nround2() == 1:
				self.game.status = 'denouement'
				self.broadcast("denouement")
			else:
				self.game.status = 'forum'
				self.game.forumreset()

# have chosen Network Interface to be steward of game.status
# is this a good choice?
class NetworkInterfaceClient(NetworkInterface):
	
	def __init__(self, game):
		self.game = game
		
	def start(self):
		#self.s = '' # socket to be connected
		#self.rx_thread = '' # rx line thread to be connected
		self.connections = {} # store of connections - for compatibility with server code
		
		# create the task queue
		# for client probably unnecessary to use Q, but just in case
		self.q = Queue.Queue()
		
		# create and start the queue handler thread
		self.q_handler_thread = threading.Thread(target = self.queue_manager, name = 'q-manager')
		self.q_handler_thread.daemon = True # so that it will not attempt to persist when the program terminates
		self.q_handler_thread.start()
		
	# iteration parameter is only used internally for repeated connection attempts
	def connect(self, iteration = 1):
		# get IP contenders (localhost, lan ip, www ip)
		try: # locate servers
			ips = urllib2.urlopen(IPS_URL).read().split()
		except: # if unable to open IPS_URL, localhost is our only shot
			logging.warning("Unable to access IPs @ %s" % IPS_URL)
			logging.warning("Only eligible IP is localhost.")
			ips = ['127.0.0.1']
		
		#debug
		print ips
		
		# try sequentially to open a host on said IP
		success = False
		for ip in ips:
			# using create_connection instead of connect because of timeout, otherwise it's eternal
			try:
				# timeout after 300ms
				# sock = socket.create_connection((ip, BONES_PORT), 0.3) # equivalent?
				sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
				sock.settimeout(0.3)
				sock.connect((ip, BONES_PORT))
				success = True
				break
			except: # socket.timeout, socket.error:
				continue
	
		# if there's a failure to connect, try up to three more time
		# 5 seconds later, then 20 seconds later, then 60 seconds later
		# configurable in constants
		if not success:
			if iteration == MAX_RECONNECT_ITERATIONS + 1:
				msg = "Unable to connect to server after %d attempts.\n" % iteration
				msg += "Terminating program..."
				self.game.ui.msg(msg, newprompt = False)
				logging.info("Failed to connect to server after %d attempts." % iteration)
				time.sleep(10) # so the user can see the message
				# for some reason sys.exit() doesn't work here
				sys.exit()
				
			delay = RECONNECT_DELAYS[iteration]
			msg = "Unable to connect to bones server.\n"
			msg += "Attempting reconnect in %d seconds." % delay
			self.game.ui.msg(msg, newprompt = False)
			time.sleep(delay)
			self.connect(iteration = iteration + 1)
			return
			
		sock.settimeout(None) # no timeout anymore
		
		rx_thread = threading.Thread(target = self.rx, args = (SERVERID, sock), name = 'rxclient')
		rx_thread.start()
		
		#TODO get sockdetails		
		self.connections[SERVERID] = (rx_thread, sock, 'sockdetails - should be here!')
		
		self.game.status = 'forum'
		
		self.tx('mynameis', self.game.localplayer().getname())
					
	# USER DEFINED 
	
	def sendwager(self, count, color):
		self.game.status = 'wagering'
		self.tx('wager', (count, color))
		print "Offer transmitted..."
		
	def acceptwager(self): self.tx('accept')
	def rejectwager(self): self.tx('reject')
		
	def newname(self, name):
		if self.game.status == 'disconnected': return
		self.tx('newname', name)
	
	def messageall(self, msg): self.tx('message', msg)
		
	def hand(self, hand): self.tx('hand', hand)
	
	# name mangled - continue is python keyword
	def continue_(self): self.tx('continue')
	def forfeit(self): self.tx('forfeit')
	def double(self): self.tx('double')
	
	# if the connection is broken, attempt to reconnect
	def broken_connection(self, id):
		msg = "Connection with server has been broken."
		msg += "Attempting to reconnect..."
		self.game.ui.msg(msg)
		
		del self.connections[id]
		self.connect()
		self.game.ui.msg("You have been reconnected to the server.")
		
	def command_handler(self, id, command, args):
		try:
			handler = eval('self.cmd_%s' % command)
		except:
			logging.warning("Channel " + str(id) + " unrecognized rx command: " + str((command,args)))
		handler(id, args)
		
	# clients is assigned an ID
	def cmd_assignID(self, id, args):
		oldid = self.game.localplayer().getid()
		newid = int(args)
		
		self.game.localplayer().setid(newid)
		self.game.localplayerid = newid
		self.game.players[newid] = self.game.players.pop(oldid)
					
	# you've just connected and the server reports the status of the current game
	# if it's anything other than forum, you've just joined mid-game
	# pretend you've been here all along, but rejected the wager for the present game
	def cmd_hold(self, id, args):
		self.game.ui.msg("Game already in progress. Please hold.")
		self.game.status = 'hold'
			
	# if there's a new player, add him to the game
	def cmd_newplayer(self, id, args):
		id, name = self.tuple_unpack(args)
		if id in self.game.players:
			return
		newplayer = Player(name)
		newplayer.setid(id)
		self.game.players[id] = newplayer
		self.game.ui.msg("%s has joined the game." % name)
					
	# if someone has changed their name, synch
	def cmd_nameadjust(self, id, args):
		id, newname = self.tuple_unpack(args)
		
		# don't bother if the change was made locally
		if id == self.game.localplayerid: return
		
		oldname = self.game.players[id].getname()
		self.game.players[id].setname(newname)
		
		self.game.ui.msg("%s has magically transformed into %s." % (oldname, newname))
		
	# someone proposed a wager
	def cmd_wagerontable(self, id, args):
		self.game.status = 'wagering'
		id, count, color = self.tuple_unpack(args)
		wager = Seeds(count, color)
		self.game.setwager(wager)
		if id == self.game.localplayerid: return
		self.game.players[id].accept()
		name = self.game.players[id].getname()
		self.game.ui.msg("%s wagers %s. Do you accept or reject?" % (name, wager))
					
	# someone accepted the wager, will actually log if necessary
	def cmd_accepts(self, id, args):
		id = int(args)
		if id == self.game.localplayerid: return
		name = self.game.players[id].getname()
		self.game.players[id].accept()
		self.game.ui.msg("%s accepts the wager." % name)
	
	# someone rejects the wager, will actually log if necessary
	def cmd_rejects(self, id, args):
		id = int(args)
		if id == self.game.localplayerid: return
		name = self.game.players[id].getname()
		self.game.players[id].reject()
		self.game.ui.msg("%s rejects the wager." % name)
		
	# there were no takers on the wager
	# OR it's the end of a game, moving to next game
	def cmd_forum(self, id, args):
		if self.game.status == 'wagering':
			self.game.ui.msg("There were no takers on that wager.")
		elif self.game.status == 'hold':
			self.game.ui.msg("Thank you for holding. You may now participate.")
		self.game.status = 'forum'
		self.game.forumreset()	
		
	# have all clients display a message
	def cmd_orate(self, id, args):
		msg = args
		self.game.ui.msg("%s" % msg)
	
	# relay a message to everyone from a particular client
	def cmd_messagerelay(self, id, args):
		id, msg = self.tuple_unpack(args)
		if id == self.game.localplayerid: return
		name = self.game.players[id].getname()
		self.game.ui.msg("%s: %s" % (name, msg))
		#print "\n%s: %s" % (name, msg)
		#sys.stdout.write(CLI_PROMPT)
	
	# there were at least two takers on a wager: proceed to round1
	def cmd_round1(self, id, args):
		self.game.status = 'round1'
		
		playernames = [player.getname() for player in self.game.accepted_players()]
		
		line1 = "Wager of %s has been accepted by %s.\n" % (self.game.wager, self.verballist(playernames))
		if self.game.localplayer().accepted():
			line2 = "Let the games begin! All players roll your bones!"
		else: # rejected
			line2 = "You will now watch them play..."
		
		self.game.ui.msg(line1 + line2)
		
	# letting us know about other players' hands
	# redundantly overwrites own, but who cares?
	def cmd_handrelay(self, id, args): # maybe cache these until appropriate state transition
		id, hand = self.tuple_unpack(args)
		self.game.players[id].sethand(hand)
						
	# everyone has rolled in round1, we're moving to the response round
	def cmd_response(self, id, args):
		# give time for the last person to see their roll
		time.sleep(2)
		
		self.game.status = 'response'
		
		# display everyone's results so far
		maxnamelength = max([len(player.getname()) for player in self.game.accepted_players()])
		player_string = " %%%ds | %%s\n" % maxnamelength
	
		# print result for each player
		lines = 'Round 1 Results:\n'
		for player in self.game.accepted_players():
			lines += player_string % (player.getname(), player.gethand())
		
		if self.game.localplayer().accepted():
			lines += '\nYou must now choose to continue, forfeit, or double.\n'
		
		# delete the final newline
		lines = lines[:-1]
		self.game.ui.msg(lines)
	
	# round 2 is here, log everyone's continue, forfeit, double results
	def cmd_responses(self, id, args):
		# redundant check
		if self.game.status != 'response': return
		
		responses = self.tuple_unpack(args)
			
		# log and report responses
		lines = ''
		for pid, response in responses:
			player = self.game.players[pid]
			if response == 'c': player.continue_()
			if response == 'f': player.forfeit()
			if response == 'd': player.double()
			
			if pid != self.game.localplayerid:
				name = player.getname()
				action_past_tense = RESPONSE_STATUS_PAST_TENSE_LUT[response]
				lines += "%s %s.\n" % (name, action_past_tense)
			
		pot = self.game.getwager() * (self.game.ndoubled() + 1) * self.game.nplayers() - self.game.getwager() * self.game.nforfeited()
		liability = self.game.getwager() * (self.game.ndoubled() + 1)
		if self.game.localplayer().forfeited():
			liability -= self.game.getwager()
		lines += "\nYou're now in for %s." % liability
		lines += "\nThe pot is now %s." % pot
							
		self.game.ui.msg(lines)
		
		# if two players are still in, go to round 2
		if self.game.nround2() >= 2:
			self.game.status = 'round2'
			if self.game.localplayer().continued() or self.game.localplayer().doubled():
				self.game.ui.msg("Roll again!")
			else:
				self.game.ui.msg("Please wait while the hard core players finish the game.")
		
		# if everyone forfeited...
		elif self.game.nround2() == 0:
			self.game.ui.msg("Everyone forfeited. It's a draw. Booooooooring.")
			self.game.status = 'forum'
			self.game.forumreset()
					
		# otherwise, it's a draw quietly wait for the denouement command
								
	def cmd_denouement(self, id, args):
		self.game.status = 'denouement'
		self.game.calcrankings()
		
		# no action required if you weren't participating
		if self.game.localplayer().rejected(): return
	
		# otherwise, you played, so figure out how much money you were in for
		liability = self.game.getwager() * (self.game.ndoubled() + 1)
		if self.game.localplayer().forfeited():
			liability -= self.game.getwager()
		contribution = self.game.localplayer().bank.withdraw(liability)
		self.game.localplayer().setcontribution(contribution)
		
		# if we're short
		if contribution != liability and self.game.localplayer() not in self.game.winners():
			short = liability - contribution
			self.game.ui.msg("You're short %s!" % short)
		
		arg_tuple = str((contribution.getcount(), contribution.getcolor()))
		self.tx("contribution", arg_tuple)
		
	# letting us know about other players' contributions
	# redundantly overwrites own, but who cares?
	def cmd_contributionrelay(self, id, args):
		id, count, color = self.tuple_unpack(args)
		self.game.players[id].setcontribution(Seeds(count, color))

	# server tells us the final financial results
	def cmd_spoils(self, id, args):
			
		# give time for the last person to see their roll
		time.sleep(2)
					
		winners = self.tuple_unpack(args)
		for id, count, color in winners:
			self.game.players[id].setincome(Seeds(count, color))	
					
		# add spoils to your bank
		self.game.localplayer().bank.deposit(self.game.localplayer().getincome())
					
		msg = self.resultstable()					
		self.game.ui.msg(msg)
					
		self.game.forumreset()
		self.game.status = 'forum'
						
	# someone's gone. Remove them from the game and reset.
	def cmd_mandown(self, id, args):
		id = int(args)
		self.game.ui.msg("%s has left the game. Resetting to forum phase." % self.game.players[id].getname())
		del self.game.players[id]
		# presumably a forum reset will come from the server shortly
		
	###########################
	### helper methods
	
	# convert a list of items into a verbal list you'd put in a sentence
	# implements Oxford comma
	# e.g. ['John'] -> "John"
	# e.g. ['John', 'Mary'] -> "John and Mary"
	# e.g. ['J','M','K'] -> "J, M, and K
	# e.g. ['Matt', 'Mark', 'Luke', 'John'] -> "Matt, Mark, Luke, and John"
	def verballist(self, items):
		if len(items) == 1:
			return items[0]
		elif len(items) == 2:
			return "%s and %s" % (items[0], items[1])
		elif len(items) == 3:
				return "%s, %s, and %s" % (items[0], items[1], items[2])
		else:
			return "%s, %s" % (items[0], self.verballist(items[1:]))
		
	# passes back a string containing the results table, newlines and all
	# reads global 'game'
	def resultstable(self):
	#e.g.
	#  Rank |  Player   | Hand | Score | Earnings  |    Net
	#-----------------------------------------------------------
	#   1   |  Vinnie   | GGG  |   1   | 6 yellows |  2 yellows
	#   1   |   Becky   | GGG  |   1   | 6 yellows |  2 yellows 
	#   3   | Christian | BGR  |   12  | 0 yellows | -4 yellows

		# get table rows in tuple format, including header row
		row1 = [('Rank', 'Player', 'Hand', 'Score', 'Earnings', 'Net')]
		otherrows = [(player.getrank(), player.getname(), player.gethand(), player.getscore(), player.getincome(), player.getnet()) for player in self.game.accepted_players()]
		otherrows.sort()
		rows = row1 + otherrows
		
		rows = map(lambda x: map(str, x), rows) # convert all items to strings
		cols = zip(*rows) # transpose to have columns
		
		# find string length of every item, max by column will be columnwidths
		# actual number is two higher counting mandatory padding of space on either side of |
		stringlengths = map(lambda x: map(len, x), cols) # find length of all strings
		colwidths = map(max, stringlengths)
		
		# helper functions, only using centered so far - define elsewhere? or static?
		# no check if len(string)>n
		def centered(string, n):
			nspaces = n - len(string)
			nleft = nspaces/2
			nright = nspaces - nleft
			return ' ' * nleft + string + ' ' * nright
		
		def leftjustified(string, n):
			nspaces = n - len(string)
			return string + ' ' * nspaces
			
		def rightjustified(string, n):
			nspaces = n - len(string)
			return ' ' * nspaces + string
			
		def justify(string, loc):
			if loc == 'c': return centered(string)
			if loc == 'r': return righjustified(string)
			if loc == 'l': return leftjustified(string)
			
		def rowjoin(strlist): return ' ' + ' | '.join(strlist) + ' '
		def rowjoind(strlist): return '-' + '-|-'.join(strlist) + '-'
		
		# format all items (centered to colwidth) and synch rows
		cols = [map(lambda x: centered(x, colwidth), column) for colwidth, column in zip(colwidths, cols)]
		rows = zip(*cols)
		
		# turns each row into a single string, and inserts line separating header
		divline = rowjoind(['-' * w for w in colwidths])
		fullrows = [rowjoin(row) for row in rows]
		fullrows = fullrows[:1] + [divline] + fullrows[1:]
		
		# join all rows on table (with newlines) so table is in a single string
		table = '\n'.join(fullrows)
		
		return table

# command line interface for client
class CLI(cmd.Cmd):
	def __init__(self, game):
		cmd.Cmd.__init__(self)
		self.prompt = CLI_PROMPT
		self.fastroll = False
		self.game = game
		
	def start(self):
		print INTRO_ART
		
		name = raw_input('Enter your name: ')
		self.do_setname(name)
		
		print('Enter your bankroll as integers:')
		y = raw_input(' Number of yellows: ')
		r = raw_input('    Number of reds: ')
		b = raw_input('   Number of blues: ')
		g = raw_input('  Number of greens: ')
		self.do_deposit(' '.join([y, r, b, g]))
		
		print "\nConnecting to server..."
		self.game.ni.connect()
		
		# consolidated print in case interrupted by message rx
		msg  = "\n"
		msg += "Welcome to the game, %s.\n\n" % self.game.localplayer().getname()
		msg += "You can make a wager, wait for more players, or wait for someone else to wager.\n"
		msg += "You can access help at any time by typing 'help'"
		print msg
		
		self.cmdloop()
	
	# print a message then show a new prompt
	def msg(self, msg, newprompt = True):
		print
		print msg
		if newprompt: sys.stdout.write(self.prompt)
	
	########################
	### STANDARD COMMANDS
	
	# ordered by relatedness, then roughly by order
	
	# close the CLI
	def do_exit(self, args):
		# disconnect, tie up loose ends, stop threads, etc. ?		
		sys.exit()
	
	# change name to ... and report change to server
	def do_setname(self, name):
		self.game.localplayer().setname(name)
		self.game.ni.newname(name)

	# deposit into seedbank
	def do_deposit(self, args):
		args = args.split()
		
		# if there are two arguments and second is a reasonable color, deposit such
		if len(args) == 2 and args[1] in COLORS:
			count, color = args
			try:
				count = int(count)
			except ValueError:
				print "Unable to convert (%s) into an integer number of seeds." % count
				return
			self.game.localplayer().bank.deposit(Seeds(count, color))
		
		# ditto if there's no space between them
		elif len(args) == 1 and args[0][-1] in COLORS:
			count, color = args[0][:-1], args[0][-1]
			try:
				count = int(count)
			except ValueError:
				print "Unable to convert (%s) into an integer number of seeds." % count
				return
			self.game.localplayer().bank.deposit(Seeds(count, color))
			
		# otherwise pray the arguments are numeric and deposit corresponding quantities
		# e.g. deposit 4 3 1 2 -> deposits 4 yellow, 3 red, 1 blue, 2 green
		elif len(args) <= len(COLORS):
			try:
				args = [int(i) for i in args]
			except:
				print "Error: Unable to parse arguments as integers."
				return
			deposits = zip(args, COLORS)
			for count, color in deposits:
				self.game.localplayer().bank.deposit(Seeds(count, color))
			
		else:
			print "Too many arguments?!?"
	
	# optimize the bank
	def do_optimize(self, args): self.game.localplayer().bank.optimize()
	
	# print player info, game info, and bank info
	def do_player(self, args): print self.game.localplayer()
	def do_status(self, args): print self.game
	def do_bank(self, args): print self.game.localplayer().bank
	
	# wager some money
	def do_wager(self, args):
		if self.game.status != 'forum':
			print "Bad time to wager (game.status = %s)..." % self.game.status
			return
				
		if self.game.nplayers() == 1:
			print "You need opponents before you can wager..."
			return
		
		args = args.split()
		
		# if there are no arguments, prompt for count/color interactively
		if len(args) == 0:
			count = raw_input("Enter the number of seeds you wager: ")
			color = raw_input("Enter the color of seeds you wager (%s): " % '/'.join(COLORS))
		
		# if there's one argument, it's combined e.g. 50y
		elif len(args) == 1:
			arg = args[0]
			count = arg[:-1]
			color = arg[-1]
			if color not in COLORS:
				print "Final argument character should be color %s." % '/'.join(COLORS)
				return
			
		# if there are two arguments, they're spaced e.g. 50 y
		elif len(args) == 2:
			count, color = args
		
		# more than two arguments?
		else: #
			print "Too many arguments."
			self.help_wager()
			return
			
		try:
			count = int(count)
		except ValueError:
			print "First argument to wager must be an integer..."
			return
		
		if count <= 0:
			print "Cannot wager less than 1 seed..."
			return

		if color not in COLORS:
			print "Invalid color (%s)..." % color
			print "Valid colors: ", '/'.join(COLORS)
			return
			
		if Seeds(count, color).value() > self.game.localplayer().bank.value():
			print "You cannot afford to wager this much."
			return
		
		self.game.setwager(Seeds(count, color))
		self.game.localplayer().accept()
		self.game.ni.sendwager(count, color)
	do_w = do_wager
	
	# accept an offered wager	
	def do_accept(self, args):
		if self.game.status != 'wagering':
			print "Not in wagering phase..."
			return
		
		if self.game.localplayer().responded_to_wager():
			print "You have already responded to the wager..."
			return
			
		if self.game.getwager().value() > self.game.localplayer().bank.value():
			print "Nice try! You cannot afford to accept this wager."
			print "Either reject the wager or put more money in your bank (with deposit command)."
			return
		
		self.game.localplayer().accept()
		self.game.ni.acceptwager()
	do_a = do_accept
	
	# reject an offered wager
	def do_reject(self, args):
		if self.game.status != 'wagering':
			print "Not in wagering phase..."
			return
		
		if self.game.localplayer().responded_to_wager():
			print "You have already responded to the wager..."
			return
					
		self.game.localplayer().reject()
		self.game.ni.rejectwager()
		
	# roll the dice
	def do_roll(self, args):
		if self.game.localplayer().rejected() or self.game.localplayer().forfeited():
			print "You're sitting this one out..."
			return
		
		if self.game.status not in ['round1', 'round2']:
			print "It does not make sense to roll at this time..."
			return # comment out to allow testing of roll during forum phase
		
		# how many rolls have happened so far?
		nrolls = self.game.localplayer().nrolls()
		
		# if we're already at two rolls in round 1, stop
		if nrolls == 2 and self.game.status == 'round1':
			print "Easy there, %s. Only two rolls for now..." % TIGER_WORD
			return
		
		# if we're already at three rolls in round 2, stop
		if nrolls == 3 and self.game.status == 'round2':
			print "Easy there, %s. Three rolls is all you get..." % TIGER_WORD
			return
			
		result = self.game.localplayer().roll()
		nrolls += 1
		
		if nrolls == 1:
			print "First roll..."	
		elif nrolls == 2:
			print "Second roll..."
		else: # nrolls == 3
			print "Final roll..."
			
		self.animateroll(DIE_COLOR_LUT[result], self.fastroll)
		
		# if two rolls (end of round1) or three rolls (end of round2) have occurred,
		# tell the server the hand
		if nrolls in [2, 3]:
			self.game.ni.hand(self.game.localplayer().gethand())

	def do_r(self, args):
		if self.game.status == 'wagering':
			self.do_reject(args)
		else:
			self.do_roll(args)
	
	# continue playing
	def do_continue(self, args):
		if self.game.status != 'response':
			print "Invalid command when game status is '%s'." % self.game.status
			return
			
		if self.game.localplayer().responded_to_cfd():
			print "You already chose to %s." % RESPONSE_STATUS_LUT[self.game.localplayer().getresponse()]
			return
			
		self.game.localplayer().continue_()
		self.game.ni.continue_()
	do_c = do_continue
	
	def do_forfeit(self, args):
		if self.game.status != 'response':
			print "Invalid command when game status is '%s'." % self.game.status
			return
			
		if self.game.localplayer().responded_to_cfd():
			print "You already chose to %s." % RESPONSE_STATUS_LUT[self.game.localplayer().getresponse()]
			return
			
		self.game.localplayer().forfeit()
		self.game.ni.forfeit()	
	do_f = do_forfeit
	
	def do_double(self, args):
		if self.game.status != 'response':
			print "Invalid command when game status is '%s'." % self.game.status
			return
			
		if self.game.localplayer().responded_to_cfd():
			print "You already chose to %s." % RESPONSE_STATUS_LUT[self.game.localplayer().getresponse()]
			return
			
		# if you've wagered half your money, you can't AFFORD to double
		if self.game.getwager().value() * 2 > self.game.localplayer().bank.value():
			print "You can't afford to double! You'd better hope no one else does!"
			return
		
		self.game.localplayer().double()
		self.game.ni.double()
	do_d = do_double
	
	# send a message to the world
	def do_message(self, args):
		msg = args
		# sanitize of pipes
		msg = msg.replace('|','')
		self.game.ni.messageall(msg)
	do_m = do_message	
	
	
	###############################
	### DEBUG / TESTING COMMANDS
	
	# names should be mangled to prevent production access
	# add/delete pre-"do" underscore to toggle
	
	# if shell (or !) then execute as if in python interpreter
	def _do_shell(self, args):
		try:
			exec args in globals()
		except:
			traceback.print_exc(file=sys.stdout)
	
	# open a new client in another window
	def _do_client(self, args): os.system('start python client.py')

	# connect to the server
	def _do_connect(self, args):
		if self.game.status == 'disconnected':
			self.game.ni.connect()
		#print "Connected to server..."
		
	# disconnect from the server
	# unimplemented
	def _do_disconnect(self, args):
		pass # self.game.ni.disconnect()
	
	# launch a server #HW
	def _do_launch(self, args):
		os.system('start python server.py')
		time.sleep(0.5)
		print "Server launched..."
			
	# perform a macro (for debug/testing)
	# Note: most of these macros are defunct due to changes in program structure
	# mainly connect occurs on CLI launch now
	def _do_macro(self, args):
		try:
			command = int(args)
		except:
			print "Need single argument: command #."
			return
			
		if command == 1:
			#self.do_launch('')
			self.do_setname('Vinnie')
			self.do_deposit('300')
			self.do_connect('')
			self.do_fastroll('')
			
		elif command == 2:
			self.do_setname('Christian')
			self.do_deposit('200')
			self.do_connect('')
			self.do_fastroll('')
			
		elif command == 3:
			self.do_setname('Becky')
			self.do_deposit('777')
			self.do_connect('')			
			self.do_fastroll('')

		elif command == 4:
			self.do_setname('Christian')
			self.do_deposit('200')
			self.do_connect('')
			self.do_fastroll('')
			time.sleep(0.5)
			self.do_wager('50 y')
			self.do_fastroll('')

		elif command == 5:
			self.do_setname('Vinnie')
			self.do_deposit('300')
			self.do_connect('')
			self.do_fastroll('')
			time.sleep(7)
			self.do_accept('')
			time.sleep(7)
			self.do_roll('')
			self.do_roll('')
			
		elif command == 6:
			self.do_setname('Christian')
			self.do_deposit('200')
			self.do_connect('')
			self.do_fastroll('')
			time.sleep(7)
			self.do_accept('')
			time.sleep(3)
			self.do_roll('')
			self.do_roll('')
			
		elif command == 7:
			self.do_setname('Becky')
			self.do_deposit('777')
			self.do_connect('')
			self.do_fastroll('')
			time.sleep(0.5)
			self.do_wager('50 y')
			time.sleep(8)
			self.do_roll('')
			self.do_roll('')
			
		elif command == 8:
			self.do_setname('Christian')
			self.do_deposit('200')
			self.do_connect('')
			self.do_fastroll('')
			time.sleep(7)
			self.do_reject('')

		else:
			print "Unrecognized command in do_macro (%d)..." % command
	do_m = _do_macro

	# toggle fastroll, or specify fastroll on / fastroll off
	def _do_fastroll(self, args):
		args = args.split()
		if args == []:
			self.fastroll = not self.fastroll
		elif args[0] == 'on':
			self.fastroll = True
		elif args[0] == 'off':
			self.fastroll = False
		else:
			print "Bad argument for fastroll: %s" % args
		print "fastroll =", self.fastroll
	
	##################
	### COMMAND HELP
	
	def help_exit(self):
		print "syntax: exit"
		print "--terminates the program"
	
	def help_setname(self):
		print "syntax: setname [name]"
		print "-- allows you to configure name"
		
	def help_deposit(self):
		print "syntax: deposit [#seeds][color]"
		print "syntax: deposit [#yellow] [#red] [#blue] [#green]"
		print "-- deposit seeds into your bank"
	
	def help_optimize(self):
		print "syntax: optimize"
		print "-- converts your bank into minimal form"
		
	def help_player(self):
		print "syntax: player"
		print "-- displays your info"
		
	def help_status(self):
		print "syntax: status"
		print "-- displays info on game and all players"
		
	def help_bank(self):
		print "syntax: bank"
		print "-- displays the contents of your bank"
		
	def help_wager(self):
		print "syntax: wager [#seeds] [color]"
		print "syntax: wager"
		print "-- initiate a game by wagering"
		print "-- color should be single character y/r/b/g"
		print "-- no space required between arguments"
		print "-- can also wager interactively sans arguments"
		
	def help_accept(self):
		print "syntax: accept"
		print "-- accept a proposed wager"
		
	def help_reject(self):
		print "syntax: reject"
		print "-- reject a proposed wager"
		
	def help_roll(self):
		print "syntax: roll"
		print "-- roll the dice!"
		
	def help_continue(self):
		print "syntax: continue"
		print "-- choose to continue after round 1 of rolls"
		
	def help_forfeit(self):
		print "syntax: forfeit"
		print "-- choose to forfeit after round 1 of rolls"
	
	def help_double(self):
		print "syntax: double"
		print "-- choose to double after round 1 of rolls"
	
	def help_message(self):
		print "syntax: message [message]"
		print "-- send a message to all other players"
		
	def help_rules(self):
		print "Rules of BONES."
		print " Forum Phase: Someone makes a wager. Other players accept or reject it."
		print " Round 1: All players who accepted the wager roll two bones."
		print "   - The bones have six sides - three red, two blue, and one green."
		print " Response Phase: Players privately decide to continue, double, or forfeit."
		print "   - Continuing does not affect the wager."
		print "   - Doubling increases everyone's commitment by the amount of the wager."
		print "   - Forfeiting reduces a player's commitment by the amount of the wager."
		print "     A player who forfeits loses by default."        
		print "     Note: If someone doubles, a forfeiting player still has a net liability."
		print " Round 2: All players roll one last bone."
		print "   - The player with the highest ranked hand wins the pot. (See help rank)"
		
	# show the chart of hands
	def help_rank(self):
		print " Rank | Hand"
		print "------|------"
		pairs = [(CODEBOOK[hand], hand) for hand in CODEBOOK]
		pairs.sort()
		for pair in pairs:
			print "  %2d  | %s" % pair
	
	######################################
	### helper methods
	
	# text animates die rolling faster, then slowing to a stop on result
	# empirically chosen a cubic model for time delays
	# animates to stdout
	def animateroll(self, result, fastroll = False):

		# don't actually animate it if fastroll is enabled
		if fastroll:
			sys.stdout.write('Result: %s\n' % result)
			return
		
		# constants empirically determined
		nsteps = 16
		step1_delay = 0.1 # seconds
		stepn_delay = 0.8 # seconds
		
		# just in case
		stepn_delay = float(stepn_delay)
		
		# max width of all colors
		fixed_width = max([len(i) for i in DIE_COLOR_NAMES])
		
		template = "Result: %%-%ds\r" % fixed_width
		
		# helper: cubic interpolation of time step
		def delay(i): return (stepn_delay - step1_delay) / nsteps ** 3 * i ** 3 + step1_delay
		
		new = ''
		for i in xrange(nsteps):
			old = new
			
			# loop until this iteration we get a color that was different from last time
			while True:
				new = random.choice(DIE_COLOR_NAMES)
				if new != old: break
			
			# update the animation, then wait
			sys.stdout.write(template % new)
			time.sleep(delay(i))
			
		sys.stdout.write(template % result)
		sys.stdout.write('\n')

# run as client if this program is run
# to run as server use server launch script
if __name__ == "__main__":
	game = GameClient()
	game.start()

