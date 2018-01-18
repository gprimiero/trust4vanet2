;; code by @jtagliabue/@gprimiero

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PROPERTIES AND GLOBALS

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; define an attacker breed to easily distinguish turtle
breed [ attackers attacker ]

turtles-own
[
  propositions  ;; LIST truth value for propositions for the turtle: -1 FALSE, 0 NEUTRAL, +1 TRUE, [0] defualt
  ranking ;; measure of turtle importance, usually function of its position in the network, -1 default
  propositionRanking ;; LIST measure of message importance, [0] default
  apperception  ;; LIST value of apperception, function of ranking and time that it came to know a given proposition [-100000.0]
  sourceTurtles ;; LIST of turtle's ID which are the source of the knowledge that P [-1] default, -2 is the attacker
  propositionsTicks  ;; LIST of timestamp when turtles get knowlegde of the truth value of proposition X [-1] default
]

links-own
[

]

;; all CAPS identifies a constant setting
globals [
  TURTLE-SIZE
  TURTLE-COLOR
  #PROPOSITIONS
]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SETUP FUNCTIONS

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to setup
  clear-all
  ;; set default values
  set TURTLE-SIZE 0.8
  set TURTLE-COLOR blue
  set #PROPOSITIONS 1
  set-default-shape turtles "circle"
  ;; read global values from interface
  let current_network_type _network_type
  let maxTurtles _nodes
  ;; if DEBUG, set values for a debug run
  if (_is-debug = true)
  [
    set TURTLE-SIZE 1
    set TURTLE-COLOR red
    set current_network_type "linear"
    set maxTurtles 6
    set #PROPOSITIONS 1
  ]
  ;; build the network of agents based on network type
  buildNetwork maxTurtles current_network_type
  ;; graph-edges to show edge distribution
  graph-edges
  reset-ticks
  ;; automatically set a discovery item if debug
  if (_is-debug = true) [ discovery 0 ]
end

;; reset values without re-generating the network
to clearP
  ;; reset turtles properties
  ask turtles [ initializeTurtle TURTLE-SIZE TURTLE-COLOR #PROPOSITIONS ]
  ;; reset knowledge plot
  set-current-plot "knowledge of prop 0"
  clear-plot
  ;; reset ticks
  reset-ticks
end

;; initialize turtles
to initializeTurtle [_size _color _prop#]
  ;; reset all variables
  set color _color
  set size _size
  set ranking -1
  set propositions []
  set apperception []
  set sourceTurtles []
  set propositionsTicks []
  set propositionRanking []
  ;; initialize belief-related variables depening on # of propositions in the system
  let counter 0
  while [counter < _prop#]
  [
    set propositions lput 0 propositions
    set apperception lput -100000.0 apperception
    set sourceTurtles lput -1 sourceTurtles
    set propositionsTicks lput -1 propositionsTicks
    set propositionRanking lput 0 propositionRanking
    set counter counter + 1
  ]
end

to buildNetwork [_turtles# _networkType]
  if (_networkType = "total") [ buildTotalNetwork _turtles# 13 ]  ;; this is a constant, for viz purposes only
  if (_networkType = "linear") [ buildLinearNetwork _turtles# ]
  if (_networkType = "random") [ buildRandomNewtork _turtles# ]
  if (_networkType = "small-world") [ buildSmallWorldNewtork _turtles# ]
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; RUNTIME FUNCTIONS

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to go
  ;; now the only proposition we are interested in is prop 0
  let propIndex 0
  ;; if no stop
  ifelse (goCondition propIndex = true) [ goStep propIndex ]
  ;; if time to stop
  [
    print "All done! See you, space cowboys!"
    ;; log if needed and stop
    if (_log) [ export-data ]
    stop
  ]
end

;; separate business logic for each model step here to re-use it in simulations
to goStep [ _propositionIndex ]
  ;; print progress if debug
  if (_is-debug = true) [ print word "Running timestep N " ticks ]
  ;; run knowledge dynamics
  spreadKnowledge _propositionIndex
  ;; advance tick
  tick
  ;; update plots
  updateRuntimePlots
end


to-report goCondition [ _propositionIndex ]
  ;; just for now, stop when every turtle has a truth val for the proposition
  report count (turtles with [ item _propositionIndex propositions = 0 ]) > 0
end

to run-sim [ _propositionIndex _sim# ]
  setup
  let counter 0
  while [ counter < _sim#]
  [
    if (_is-debug = true) [ print word "Running simulation N " counter ]
    clearP
    discovery _propositionIndex
    while [ goCondition _propositionIndex = true ]
    [
      ;; check if the network coverage exceed the attack treshold
      let proportionKnowlegde (count turtles with [ item _propositionIndex propositions > 0 ]) / (count turtles)
      if (proportionKnowlegde >= network_coverage_for_attack)
      [
        if (_is-debug = true) [ print (word "Prop. knowlegde of " proportionKnowlegde " exceed attack trehsold: " network_coverage_for_attack) ]
        attack _propositionIndex
      ]
      ;; spread knowledge
      goStep _propositionIndex
    ]
    ;; finally export data
    export-data
    ;; update counter
    set counter counter + 1
  ]
end

to discovery [ _propositionIndex ]
  ask one-of turtles [ knowProposition _propositionIndex -1 1 ]
end

to spreadKnowledge [ _propositionIndex ]
  ;; ask one of the turtle that know the propositon of interest or its negation
  ask turtles with [ item _propositionIndex propositions != 0 ]
  [
    ;; try to spread the info about P to turtles connected
    let myId who
    let truthVal item _propositionIndex propositions
    ask one-of link-neighbors [ knowProposition _propositionIndex myId truthVal ]
  ]
end

to attack [ _propositionIndex ]
  ;; ask N turtles that knows that P to flip truth value to spread the negation of P
  ask n-of number_attacker turtles with [ item _propositionIndex propositions = 1 ]
  [
    ;; set the breed
    set breed attackers
    knowProposition _propositionIndex -2 -1
  ]
end

to knowProposition [ _propositionIndex _source _truthValue ]
  if (_is-debug = true) [ print (word "Turtle " who " get to know proposition with index " _propositionIndex " from source turtle " _source " and truth value " _truthValue) ]
  let proposition_timestamp ticks
  ;; set the timestamp value
  set propositionsTicks replace-item _propositionIndex propositionsTicks proposition_timestamp
  ;; set source value
  set sourceTurtles replace-item _propositionIndex sourceTurtles _source
  ;; set ranking for the message
  set propositionRanking replace-item _propositionIndex propositionRanking rankP ;; read value from slider
  ;; set apperception value: avoid a 0 apperception value by setting 1 as min timestamp
  let currentApperception calculateApperceptionValue (ranking) (item _propositionIndex propositionRanking) (proposition_timestamp + 1)
  set apperception replace-item _propositionIndex apperception currentApperception
  ;; finally, set the belief truth value of the proposition for the turtle
  ;; depending on a verification process involving current value and the source of new information
  ;; first, set as default the truth value received in input (if no source, set directly the truth value)
  let finalTruthValue _truthValue
  ;; if there is a source, verify info
  if (_source >= 0)
  [
    let currentTruthValue item _propositionIndex propositions
    set finalTruthValue verifyProposition currentTruthValue _truthValue _propositionIndex breed who _source
    if (_is-debug = true) [ print (word "Old truth val: " currentTruthValue " , proposed truth val: " _truthValue " final: " finalTruthValue) ]
  ]
  set propositions replace-item _propositionIndex propositions finalTruthValue
  ;; for debug purposes, print them out
  if (_is-debug = true) [
    print word "propositions " propositions
    print word "proposition timestamp " propositionsTicks
    print word "sources " sourceTurtles
    print word "proposition ranking " propositionRanking
    print word "turtle ranking " ranking
    print word "apperception " apperception
    print word "breed " breed
  ]
  ;; change color depending on truth value for viz purposes
  if (finalTruthValue = 1) [ set color green ]
  if (finalTruthValue = -1) [ set color magenta ]
end

to-report verifyProposition [ _currentVal _newVal _propositionIndex _breed _currentWho _sourceWho]
  ;;;;; get properties for current and source turtle
  ;;;;;

  ;; get apperception values
  let sourceApperception getApperceptionFromWho _sourceWho _propositionIndex
  let currentApperception item _propositionIndex apperception
  if (_is-debug = true) [ print (word "Apperception of source turtle: " sourceApperception " , apperception of current turtle: " currentApperception) ]
  ;; get ranking values
  let sourceRanking item 0 [ranking] of turtles with [ who = _sourceWho]
  let currentRanking ranking
  if (_is-debug = true) [ print (word "source ranking, current ranking: " sourceRanking ", " currentRanking) ]

  ;;;;; now, reason by case
  ;;;;;

  ;; if it is an attacker, it won't change its mind
  if (_breed = attackers)
  [ report _currentVal ]

  ;; if the turtle has same info on P, just return the same val for now (later we can think of strengthening the degree of belief)
  if (_currentVal = _newVal)
  [ report _newVal ]

  ;; if the turtle has no prior info on P, use reputation to decide what to do
  if (_currentVal = 0)
  [
    ;; if app source >= my app, accept the new info as the truth
    ifelse (sourceApperception >= currentApperception)
    [ report _newVal ]
    [ report 0 ]
    ]


  ;; if the turtle has opposite info on P, use the resolution rule
  if (_currentVal != _newVal)
  [
    ;; report current value if current APP > source APP
    ifelse (sourceApperception = currentApperception)
      [let consensus neighborConsensus _propositionIndex _newVal _sourceWho
      ;; check neighbors -  if they agree, do not change mind
      ifelse (consensus = false)
      [ report _currentVal ]
      ;; change mind vice versa
      [ report _newVal ]

    ]
    ;; do not change mind vice versa
    [ report _currentVal ]
  ]
end


;; to compute for a turtle with P the value of the apperception of p by an agent s
;; as a function of the ranking of p and the time at which p is known
to-report calculateApperceptionValue [ sourceRanking _propositionRanking _tick ]
  report (1.0 * sourceRanking) * (1.0 * _propositionRanking ) * ( _tick * 1.0)
end


;; return the apperception value for P based on a turtle id (who)
to-report getApperceptionFromWho [ _who _propositionIndex ]
   ;; we get item 0 here as the reporter will return a list containing a list, since "who" is a unique id among turtles
  let sourceApperceptionList item 0 [apperception] of turtles with [ who = _who]
  ;; from the apperception list of the source turtle, read the info about the current P
  report item _propositionIndex sourceApperceptionList
end

to-report neighborConsensus [ _propositionIndex _truthVal _sourceWho ]
  let sourceApperception getApperceptionFromWho _sourceWho _propositionIndex
  let total_neighbors_with_opinion count link-neighbors with [item _propositionIndex propositions != 0 and item _propositionIndex apperception <= sourceApperception]
  let total_neighbors_with_same_opinion
  ;count link-neighbors with [item _propositionIndex propositions = _truthVal and item _propositionIndex apperception <=  my_apperception]
  count link-neighbors with [item _propositionIndex propositions != 0 and item _propositionIndex apperception > sourceApperception ]
  ;; first check if there are relevent neigh at all
  if (total_neighbors_with_opinion = 0) [ report false]
  ;; if there are, compare number of total neigh with number of neigh with same opinion
  ifelse (total_neighbors_with_opinion = total_neighbors_with_same_opinion) [ report true ]
  [ report false ]
  ;
;  let total_neighbors_with_opinion count link-neighbors with [item _propositionIndex propositions != 0 ]
;  let total_neighbors_with_greater_app count total_neighbors_with_opinion with [ item _propositionIndex apperception <= sourceApperception]
;  let total_neighbors_with_same_opinion count total_neighbors_with_greater_app with [item _propositionIndex propositions = _truthVal ]
;  ;; first check if there are relevent neigh at all
;  if (total_neighbors_with_opinion = 0) [ report false]
;  ;; if there are, compare number of total neigh with number of neigh with same opinion
;  ifelse (total_neighbors_with_greater_app = total_neighbors_with_same_opinion) [ report true ]
;  [ report false ]
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; NETWORK GENERATION FUNCTIONS

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to buildTotalNetwork [_turtles# _layoutRadius]
  ;; create turtles first and set all rankings to 0
  create-turtles _turtles#
  [
    initializeTurtle TURTLE-SIZE TURTLE-COLOR #PROPOSITIONS
    set ranking 0
  ]
  ;; ask turtles to get a link with each other turtle
  ask turtles [ create-links-with other turtles ]
  ;; pretty print the layout
  layout-circle turtles _layoutRadius
end

to buildLinearNetwork [_turtles#]
  ;; check that the number of turtles < total number of patches
  if (world-height * world-width < _turtles#) [ set _turtles# world-height * world-width ]
  ;; local counter to keep track of incremental creation of turtles
  let counter 0
  let newX 0
  let newY world-height - 1
  ;; create turtles
  create-turtles _turtles#
  [
    ;; initialize turtle, set ranking=counter and set position on the grid
    initializeTurtle TURTLE-SIZE TURTLE-COLOR #PROPOSITIONS
    set ranking counter
    setxy newX newY
    ;; update position counters
    set newX newX + 1
    if (newX = world-width)
    [
      set newX 0
      set newY newY - 1
    ]
    ;; update ranking counter
    set counter counter + 1
  ]
  ;; create links: each turtle is linked to turtles with (ranking = my ranking + 1)
  ask turtles
  [
    let r ranking
    create-links-with turtles with [ ranking = r + 1 ]
   ]
end

to buildRandomNewtork [_turtles#]
  ;; create turtles with random ranking and random position
  create-turtles _turtles# [
    initializeTurtle TURTLE-SIZE TURTLE-COLOR #PROPOSITIONS
    set ranking who
    setxy random-pxcor random-pycor
  ]
  ;;draw network
  ;; ask a portion of turtles to create a "seed" for the network generation
  ask n-of round (count turtles * 0.45) turtles with [count link-neighbors = 0]  [ create-link-with one-of other turtles ]
  ;;draw network by randomly add edges between nodes
  let total-edges round (count turtles)
  let counterEdges 0
  while [counterEdges <= total-edges]
  [
    ask one-of turtles
    [
      ask one-of other turtles with [count link-neighbors > 0] [ create-link-with myself ]
    ]
    set counterEdges counterEdges + 1
  ]
  ;; avoid turtles not connected
  ask turtles with [count link-neighbors = 0]  [ create-link-with one-of other turtles with [count link-neighbors > 0] ]
  ;; pretty print the layout
  layout-radial turtles links max-one-of turtles [count link-neighbors]
  ;; finally make sure to scale turtle size
  scaleTurtleSize
end

to buildSmallWorldNewtork [_turtles#]
  create-turtles 3 [ initializeTurtle TURTLE-SIZE TURTLE-COLOR #PROPOSITIONS ]
  ask turtle 0 [ create-link-with one-of other turtles ]
  ask one-of turtles with [count link-neighbors = 0] [ create-link-with one-of other turtles ]
  ;; add new node using albert-barabasi method
  while [count turtles < (_turtles# + 1)]
  [
     create-turtles 1
     [
       initializeTurtle TURTLE-SIZE TURTLE-COLOR #PROPOSITIONS
       create-link-with find-partner
     ]
  ]
  ;; set ranking proportional to the # links, the < the better
  ask turtles [ set ranking 1 / count link-neighbors ]
  ;; pretty print the layout
  layout-radial turtles links max-one-of turtles [count link-neighbors]
  ;; finally make sure to scale turtle size
  scaleTurtleSize
end

;; function needed to build a small-world network
to-report find-partner
  let total random-float sum [count link-neighbors] of turtles
  let partner nobody
  let q 0
  while [q < count turtles]
  [
    ask turtle q
    [
      let nc count link-neighbors
      ;; if there's no winner yet...
      if partner = nobody
      [
        ifelse nc > total [ set partner self ]
        [ set total total - nc ]
      ]
    ]
    set q q + 1
  ]
  report partner
end

;; scale turtle for visualization purposes
to scaleTurtleSize
  let factor 1.5 / ((max [count link-neighbors] of turtles) - (min [count link-neighbors] of turtles))
  ask turtles [ set size 0.5 + (count link-neighbors * factor) ]
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LOGGING FUNCTIONS

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Export data in tables for analysis.
to export-data
  print "Now exporting data..."
  ;;Decide on a separator
  let field_delimiter "\t"
  ;;The current time is used to generate the series of tables of a model run.
  let _filename date-and-time
  ;;Format the name in order not to have problem with windows constraints.
  set _filename remove "." (remove ":" _filename)
  set _filename word _filename ".txt"
  ;;Open the file
  file-open _filename
  ;;Header containing model parameters
  file-print "model parameters"
  file-print composeLineForFile "nodes" field_delimiter _nodes
  file-print composeLineForFile "network type" field_delimiter _network_type
  ;;Empty line
  file-print ""
  ;;Data
  file-print "model output"
  file-print composeLineForFile "total timesteps" field_delimiter ticks
  file-close
end

to-report composeLineForFile [key separator val]
  report (word key "\t" val)
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PLOT DRAWING FUNCTIONS

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to updateRuntimePlots
  draw-knowledgeable
end

to draw-knowledgeable
  set-current-plot "knowledge of prop 0"
  let perc-knowledgeable ((100 * (count turtles with [ item 0 propositions > 0 ])) / (count turtles))
  plot perc-knowledgeable
end

to graph-edges
  set-current-plot "edge-distribution"
  set-plot-x-range 1  1 + max [count link-neighbors] of turtles
  histogram [count link-neighbors] of turtles
end
@#$#@#$#@
GRAPHICS-WINDOW
267
10
585
339
-1
-1
10.0
1
10
1
1
1
0
0
0
1
0
30
0
31
0
0
1
ticks
30.0

BUTTON
607
14
670
47
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

CHOOSER
17
13
155
58
_network_type
_network_type
"total" "random" "small-world" "linear"
2

SLIDER
17
81
126
114
_nodes
_nodes
10
300
50.0
10
1
NIL
HORIZONTAL

PLOT
1027
10
1187
130
edge-distribution
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 1 -16777216 true "" ""

MONITOR
956
61
1013
106
edges
count links
17
1
11

PLOT
1026
148
1187
282
knowledge of prop 0
time-step
perc. infected
0.0
10.0
0.0
100.0
true
false
"" ""
PENS
"default" 1.0 0 -5825686 true "" ""

BUTTON
606
61
742
94
discovery prop 0
discovery 0
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
761
14
824
47
NIL
go
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
754
61
867
94
attack prop 0
attack 0
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
681
14
744
47
clearP
clearP
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
921
10
1014
55
NIL
count turtles
17
1
11

SWITCH
168
17
258
50
_log
_log
1
1
-1000

SWITCH
605
109
725
142
_is-debug
_is-debug
1
1
-1000

BUTTON
16
135
112
168
simulation
run-sim 0 1
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
17
181
222
214
network_coverage_for_attack
network_coverage_for_attack
0.0
1
0.2
0.1
1
NIL
HORIZONTAL

TEXTBOX
18
227
227
332
Simulation will automatically do setup -> discovery -> continuous run -> attack -> stop -> export\n\nIf you run the sequence manually, discovery and attack needs to be triggered MANUALLY with the buttons.
11
0.0
1

SLIDER
125
136
257
169
number_attacker
number_attacker
1
10
2.0
1
1
NIL
HORIZONTAL

TEXTBOX
605
151
755
235
If debug is enabled, some options (notably, network structure) are overriden at setup time and the console will print some verbose logging.
11
0.0
1

SLIDER
140
81
235
114
rankP
rankP
0.0
1.0
0.8
0.1
1
NIL
HORIZONTAL

MONITOR
904
148
1017
193
count % infected
(count turtles with [ item 0 propositions = -1 ]) * 1.0 /\n(count turtles) * 1.0
17
1
11

@#$#@#$#@
## WHAT IS IT?

This section could give a general understanding of what the model is trying to show or explain.

## HOW IT WORKS

This section could explain what rules the agents use to create the overall behavior of the model.

## HOW TO USE IT

This section could explain how to use the model, including a description of each of the items in the interface tab.

## THINGS TO NOTICE

This section could give some ideas of things for the user to notice while running the model.

## THINGS TO TRY

This section could give some ideas of things for the user to try to do (move sliders, switches, etc.) with the model.

## EXTENDING THE MODEL

This section could give some ideas of things to add or change in the procedures tab to make the model more complicated, detailed, accurate, etc.

## NETLOGO FEATURES

This section could point out any especially interesting or unusual features of NetLogo that the model makes use of, particularly in the Procedures tab.  It might also point out places where workarounds were needed because of missing features.

## RELATED MODELS

This section could give the names of models in the NetLogo Models Library or elsewhere which are of related interest.

## CREDITS AND REFERENCES

This section could contain a reference to the model's URL on the web if it has one, as well as any other necessary credits or references.
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
0
Rectangle -7500403 true true 151 225 180 285
Rectangle -7500403 true true 47 225 75 285
Rectangle -7500403 true true 15 75 210 225
Circle -7500403 true true 135 75 150
Circle -16777216 true false 165 76 116

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.0
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="experiment2_distrust300sw_lazyproportion10" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2_distrust300sw_lazyproportion30" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2_distrust300sw_lazyproportion50" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2_distrust300sw_lazyproportion80" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2_distrust300sw_lazyproportion100" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2b_distrust300sw_lazyproportion50_skepticskeptic" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;skepticP-skepticNotP&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2b_distrust300sw_lazyproportion50_lazylazy" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;lazyP-lazyNotP&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2b_distrust300sw_lazyproportion50_lazyskeptic" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;lazyP-skepticNotP&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2_distrust10sw_lazy300" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment2_distrust10sw_lazy" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust10sw_lazy" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust30sw_lazy" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust50sw_lazy" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust80sw_lazy" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="80"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust100sw_lazy" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust10sw_lazy200" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust10sw_lazy100" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust10sw_lazy50" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust10sw_lazy40" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="40"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust10sw_lazy30" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust300sw_balanced" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust200sw_balanced" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust100sw_balanced" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust50sw_balanced" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust40sw_balanced" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="40"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust30sw_balanced" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust300sw_sceptic" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="300"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust200sw_sceptic" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="200"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust100sw_sceptic" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust50sw_sceptic" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust40sw_sceptic" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="40"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="experiment3_distrust30sw_sceptic" repetitions="100" runMetricsEveryStep="false">
    <setup>partial_setup
contradictory-discovery</setup>
    <go>go</go>
    <timeLimit steps="1000"/>
    <metric>count turtles</metric>
    <metric>count turtles with [ p? ]</metric>
    <metric>count turtles with [ _p? ]</metric>
    <metric>[ranking] of turtle discoverP</metric>
    <metric>[ranking] of turtle discoverNotP</metric>
    <metric>sum [costsTrust] of turtles</metric>
    <metric>sum [costsDisTrust] of turtles</metric>
    <metric>count links with [color = yellow]</metric>
    <metric>count links with [color = green]</metric>
    <enumeratedValueSet variable="_log">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="discovery_type">
      <value value="&quot;random&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_exportMovie">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="proportionSkeptic">
      <value value="90"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;small-world&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="30"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="confirmationSkeptic">
      <value value="95"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="1stconfig_50nodesNEWMODEL2_TOTAL" repetitions="10" runMetricsEveryStep="true">
    <go>run-sim 0 1</go>
    <timeLimit steps="1000"/>
    <metric>(count turtles with [ item 0 propositions = -1 ]) * 1.0 / (count turtles) * 1.0</metric>
    <enumeratedValueSet variable="rankP">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_is-debug">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_network_type">
      <value value="&quot;total&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="network_coverage_for_attack">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_log">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="_nodes">
      <value value="50"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="number_attacker">
      <value value="1"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
