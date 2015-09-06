#!/bin/sh
#
# Makefile for building a suffix array test program.  This is to 
# compensate for the lack of pre-existing Makefile .
#
# This file and the associated software is of unknown legal status and
# unknown licensing
#

##GLOBAL VARIABLES######################################################

CFLAGS = -O3 -march=native -Wall

SOURCE = archon3r3.c

EXEC = archon3


##STANDARD BUILD########################################################

all : $(SOURCE)
	gcc $(CFLAGS) $(SOURCE) -o $(EXEC)

clean :
	rm -f $(EXEC)
