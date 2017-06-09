;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; GNU GENERAL PUBLIC LICENSE ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ABED-2x2-rep
;; ABED-2x2-rep (Agent-Based Evolutionary Dynamics in 2x2 repeated games)
;; is a modeling framework designed to simulate the evolution of
;; a population of agents who play a repeated symmetric 2-player game and,
;; from time to time, are given the opportunity to revise their strategy.
;; Copyright (C) 2017 Luis R. Izquierdo, Segismundo S. Izquierdo & Bill Sandholm
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;; Contact information:
;; Luis R. Izquierdo
;;   University of Burgos, Spain.
;;   e-mail: lrizquierdo@ubu.es

extensions [rnd]
;; for rnd:weighted-one-of, for clarity of code
;; (this can be done equally efficiently using rd-index-by-weights-from)

;;;;;;;;;;;;;;;;;
;;; Variables ;;;
;;;;;;;;;;;;;;;;;

globals [
  C D ;; the two actions

  ;; plotting
  ticks-per-second
  plotting-period
  second-to-plot

  ;; tasks
  follow-rule
  update-payoff
  update-candidates-and-payoffs
  update-counterparts
  reported-counterparts
  tie-winner-in

  ;; for proportional
  rate-scaling
  max-column-difference-payoffs   ;; for efficiency
  max-min-payoffs                 ;; for efficiency

  max-n-to-consider-imitating ;; for imitative protocols

  possible-numbers-of-CCs ;; for efficiency

  list-of-parameters ;; to save and load parameters

  n-of-CC-outcomes
  n-of-DD-outcomes
  n-of-outcomes

  n-of-CC-outcomes-in-match
  n-of-CC-outcomes-histogram
]


breed [players player]
breed [strategies strategy]
breed [nodes node]

players-own [
  my-strategy   ;; a pointer to a strategy-agent
  my-next-strategy ;; to model synchronous revision

  other-agents ;; this agentset is defined just for efficiency,
               ;; useful when computing update-n-of-outcomes.

  population-to-play-with
               ;; agentset with the agents to play with:
               ;; either all "players" (if self-matching?) or other "players" (if not self-matching?)

  candidates   ;; agentset containing the group of strategies you are going to select from.
               ;; strategies are unique objects that are never shared by two different agents,
               ;; even if the trees are identical. Because of this, candidates can be
               ;; an agentset rather than a list (even though agentsets cannot contain duplicates).
]


;;;;;;;;;;;;;;;;;;
;;; STRATEGIES ;;;
;;;;;;;;;;;;;;;;;;

;; A strategy is defined by a tree of nodes.
;; The first node dictates what to do in the first round.
;; Every node points to two nodes, one that will be followed if the
;; partner plays C, and another one that is followed otherwise.

strategies-own [
  my-player    ;; the player who onws the strategy
  first-node   ;; first node of the tree
  payoff       ;; this is the average payoff per match
  counterparts ;; agentset with the strategies to play with.
               ;; strategies are unique objects that are never shared by two different agents,
               ;; even if the trees are identical. Because of this, counterparts can be
               ;; an agentset (even though they cannot contain duplicates) rather than a list.

  played?      ;; true if the strategy has played in this tick, false otherwise
]

nodes-own [
  action ;; either C or D
  next-node-if-partner-played-C
  next-node-if-partner-played-D
  n-of-descendents
]

to-report new-random-strategy
  let me self
  let new nobody
  hatch-strategies 1 [
    set first-node new-node
    set payoff -1
    set counterparts nobody
    set played? false
    set new self
    set my-player me
  ]
  report new
end

to-report new-node
  let new nobody
  hatch-nodes 1 [
    set action random 2
    set next-node-if-partner-played-C nobody
    set next-node-if-partner-played-D nobody
    set new self
  ]
  report new
end

to-report new-TFT-strategy
  let new new-random-strategy
  ask new [
    ask first-node [die]
    set first-node new-TFT-node-with-action-?-from-round-? C 1
  ]
  report new
end

to-report new-TFT-node-with-action-?-from-round-? [a r]
  let new new-node
  ask new [
    set action a
    if r < n-of-rounds [
      set next-node-if-partner-played-C new-TFT-node-with-action-?-from-round-? C (r + 1)
      set next-node-if-partner-played-D new-TFT-node-with-action-?-from-round-? D (r + 1)
    ]
  ]
  report new
end

to play-vs-list-of-strategies [list-of-strategies]
  set payoff 0
  foreach list-of-strategies [[s] ->
    play-vs-strategy s
  ]
  set payoff (payoff / length list-of-strategies)
end

;; All the data in the following 2 procedures is collected only for plotting purposes.
;; Consider creating two versions of the procedures to increase speed.
;; (the most demanding line is the last line in the following procedure)

to play-vs-strategy [str]
  set n-of-CC-outcomes-in-match 0

  let my-current-node first-node
  let her-current-node ([first-node] of str)
  let my-action [action] of my-current-node
  let her-action [action] of her-current-node
  let this-match-payoff payoff-for my-action her-action

  repeat (n-of-rounds - 1) [
    set my-current-node next-node-to-?-if-partner-action-is-? my-current-node her-action
    set her-current-node next-node-to-?-if-partner-action-is-? her-current-node my-action

    set my-action [action] of my-current-node
    set her-action [action] of her-current-node
    set this-match-payoff (this-match-payoff + payoff-for my-action her-action)
  ]

  set payoff (payoff + this-match-payoff)

  set n-of-CC-outcomes-histogram add-one-in-pos-?1-of-list-?2 n-of-CC-outcomes-in-match n-of-CC-outcomes-histogram
end

to-report payoff-for [my-action her-action]
  set n-of-outcomes (n-of-outcomes + 1)

  ifelse (my-action = C)
    [ifelse (her-action = C)
      [
        set n-of-CC-outcomes (n-of-CC-outcomes + 1)
        set n-of-CC-outcomes-in-match (n-of-CC-outcomes-in-match + 1)
        report CC-payoff
      ]
      [report CD-payoff]
    ]
    [ifelse (her-action = C)
      [report DC-payoff]
      [set n-of-DD-outcomes (n-of-DD-outcomes + 1) report DD-payoff]
    ]
end

to-report next-node-to-?-if-partner-action-is-? [current-node her-action]
  let next-node nobody
  if-else (her-action = C)
    [
      set next-node [next-node-if-partner-played-C] of current-node
      if next-node = nobody [
        let new new-node
        ask current-node [set next-node-if-partner-played-C new]
        set next-node new
      ]
    ]
    [
      set next-node [next-node-if-partner-played-D] of current-node
      if next-node = nobody [
        let new new-node
        ask current-node [set next-node-if-partner-played-D new]
        set next-node new
      ]
    ]
  report next-node
end

to kill-yourself
  ask first-node [ kill-descendents die ]
  die
end

to kill-descendents
  if next-node-if-partner-played-C != nobody [ask next-node-if-partner-played-C [kill-descendents die]]
  if next-node-if-partner-played-D != nobody [ask next-node-if-partner-played-D [kill-descendents die]]
end

to-report new-strategy-copy-of [str]
  let me self
  let new nobody
  ask str [ hatch-strategies 1 [
    set first-node new-node-copy-of [first-node] of str
    set new self
    set my-player me
    ]
  ]
  report new
end

to-report new-node-copy-of [n]
  ;; this procedure creates the whole subtree from node n
  let new nobody
  hatch-nodes 1 [
    set action [action] of n
    set next-node-if-partner-played-C ifelse-value ([next-node-if-partner-played-C] of n = nobody)
      [nobody]
      [new-node-copy-of [next-node-if-partner-played-C] of n]
    set next-node-if-partner-played-D ifelse-value ([next-node-if-partner-played-D] of n = nobody)
      [nobody]
      [new-node-copy-of [next-node-if-partner-played-D] of n]
    set new self
  ]
  report new
end

to draw [str]
  display
  clear-patches
  draw-node-?-from-patch-? ([first-node] of str) (patch (2 ^ 9 - 1) 0)
end

to draw-node-?-from-patch-? [n p]
  let x [pxcor] of p
  let r (- ([pycor] of p) / 10) + 1
  ask patches with [ -10 * r < pycor and pycor < -10 * (r - 1) and (x - 2 ^ (10 - r)) < pxcor and pxcor < (x + 2 ^ (10 - r))] [set pcolor 65 - 50 * [action] of n]
  if ([next-node-if-partner-played-C] of n != nobody) [draw-node-?-from-patch-? ([next-node-if-partner-played-C] of n) (patch (x - 2 ^ (9 - r)) (- 10 * r))]
  if ([next-node-if-partner-played-D] of n != nobody) [draw-node-?-from-patch-? ([next-node-if-partner-played-D] of n) (patch (x + 2 ^ (9 - r)) (- 10 * r))]
end

to update-strategy-n-of-descendents
  ask first-node [
    ifelse n-of-rounds <= 1
      [set n-of-descendents 1]
      [
        if (next-node-if-partner-played-C != nobody or next-node-if-partner-played-D != nobody)
          [update-node-n-of-descendents]
      ]
  ]
end

to update-node-n-of-descendents
  set n-of-descendents 0
  ifelse (next-node-if-partner-played-C = nobody and next-node-if-partner-played-D = nobody)
  [ ;; final node
    set n-of-descendents 1
  ]
  [
    if next-node-if-partner-played-C != nobody [
      ask next-node-if-partner-played-C [update-node-n-of-descendents]
      set n-of-descendents (n-of-descendents + [n-of-descendents] of next-node-if-partner-played-C)
    ]
    if next-node-if-partner-played-D != nobody [
      ask next-node-if-partner-played-D [update-node-n-of-descendents]
      set n-of-descendents (n-of-descendents + [n-of-descendents] of next-node-if-partner-played-D)
    ]
  ]
end

;;;;;;;;;;;;;;;;;;;;;;;;
;;; Setup Procedures ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

to startup
  clear-all
  no-display

  setup-variables
  setup-agents
  setup-dynamics

  update-ticks-per-second

  reset-ticks
  setup-graphs

  setup-list-of-parameters
end

to setup-variables
  set C 0
  set D 1
  set possible-numbers-of-CCs range (n-of-rounds + 1)
  set n-of-CC-outcomes-histogram n-values (n-of-rounds + 1) [0]

  ;; for efficiency
  set max-column-difference-payoffs n-of-rounds * max ( list (abs (CC-payoff - DC-payoff)) (abs (CD-payoff - DD-payoff)) )
  let payoffs-list (list CC-payoff CD-payoff DC-payoff DD-payoff)
  set max-min-payoffs n-of-rounds * (max payoffs-list - min payoffs-list)
  update-rate-scaling
end

to update-rate-scaling
  set rate-scaling ifelse-value (complete-matching? or (single-sample? and candidate-selection = "direct"))
    [max-column-difference-payoffs]
    [max-min-payoffs]
end

to setup-agents
  create-players n-of-agents [
    set my-strategy runresult (word "new-" initial-condition "-strategy") ;; inneficient, but beautiful :D
    set my-next-strategy my-strategy ;; to make sure that if you do not change next-strategy, you keep the same strategy
    set hidden? true
  ]

  ask players [
    set other-agents other players
  ]
  set n-of-revisions-per-tick min (list n-of-revisions-per-tick n-of-agents)
end

to setup-dynamics

  ;; SELECT YOUR NEXT STRATEGY DIRECTLY, OR VIA IMITATION
  ifelse (candidate-selection = "direct")
    [ set update-candidates-and-payoffs [ [] -> update-candidate-strategies-and-payoffs ] ]
    [ set update-candidates-and-payoffs [ [] -> update-candidate-agents-and-payoffs ] ]

  ;; NUMBER OF STRATEGIES YOU WILL TEST (ONLY RELEVANT IN DIRECT PROTOCOLS)
  if n-of-rounds <= 3 [
    set n-in-test-set min list n-in-test-set (2 ^ (2 ^ n-of-rounds - 1))
  ]
  ;; The number of nodes in the decision tree is 2^0 + 2^1 + ... + 2^(n-of-rounds - 1)= 2^n-of-rounds - 1.
  ;; Each node can have action C or D.

  ;; NUMBER OF AGENTS YOU WILL CONSIDER FOR IMITATION (ONLY RELEVANT IN IMITATIVE PROTOCOLS)
  set n-to-consider-imitating min list n-to-consider-imitating (n-of-agents - 1)
  set max-n-to-consider-imitating min list 10 (n-of-agents - 1)

  ;; RULE USED TO SELECT AMONG DIFFERENT CANDIDATES
  set follow-rule runresult (word "[ [] -> " decision-method " ]")

  ;; UPDATE RATE-SCALING
  if decision-method = "proportional" [update-rate-scaling]

  ;; TIE-BREAKER
  set tie-winner-in runresult (word "[ [x] -> " tie-breaker " x ]")

  ;; DO YOU PLAY YOURSELF?
  ifelse self-matching?
    [ ask players [ set population-to-play-with players ] ]
    [ ask players [ set population-to-play-with other players ] ]

  if not trials-with-replacement? [
    set n-of-trials min list n-of-trials (n-of-agents - ifelse-value self-matching? [0][1])
  ]

  ;; DO YOU PLAY EVERYONE?
  ifelse complete-matching?
    [
      set update-payoff [ [] -> update-payoff-full-matching ]
      set n-of-trials ifelse-value self-matching? [count players] [count players - 1]
      set trials-with-replacement? false
      set single-sample? true
    ]
    [ set update-payoff [ [] -> update-payoff-not-full-matching ] ]

  ;; DO YOU DRAW A DIFFERENT SAMPLE OF AGENTS TO PLAY WITH EVERY TIME YOU TEST A STRATEGY,
  ;; OR JUST ONE SINGLE SAMPLE FOR ALL YOUR TESTS? (ONLY RELEVANT IN DIRECT PROTOCOLS)
  ifelse single-sample?
    [ set reported-counterparts [ [] -> fixed-counterparts ] ]
    [ set reported-counterparts [ [] -> variable-counterparts ] ]

  ;; DO YOU SELECT THE AGENTS YOU ARE GOING TO PLAY WITH REPLACEMENT OR WITHOUT REPLACEMENT?
  ifelse trials-with-replacement?
    [set update-counterparts [ [] -> update-counterparts-with-replacement ] ]
    [set update-counterparts [ [] -> update-counterparts-without-replacement ] ]

end

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Run-time procedures ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

to go

  ;; the following two lines can be commented out if parameter values are not
  ;; going to change over the course of the simulation
  setup-dynamics
  update-ticks-per-second

  ask strategies [set played? false]

  ifelse use-prob-revision?
    [ask players with [random-float 1 < prob-revision] [update-strategy]]
    [ask n-of n-of-revisions-per-tick players [update-strategy]]

  tick
  ask players [
    if (my-next-strategy != my-strategy) [ask my-strategy [kill-yourself]]
    set my-strategy my-next-strategy
  ]

  if (ticks mod (ceiling plotting-period) = 0) [update-graphs]

  update-num-agents

end

to update-ticks-per-second
  ;; it is assumed that, on average, all agents revise once per second
  set ticks-per-second ifelse-value use-prob-revision?
    [ 1 / prob-revision]
    [ n-of-agents / n-of-revisions-per-tick]

  if plot-every-?-secs < 1 / ticks-per-second [set plot-every-?-secs 1 / ticks-per-second]
  set plotting-period (ticks-per-second * plot-every-?-secs)
end

to update-num-agents
  let diff (n-of-agents - count players)

  if diff != 0 [
    ifelse diff > 0
    [ repeat diff [ ask one-of players [hatch-players 1 [
      set my-strategy new-strategy-copy-of my-strategy
      set my-next-strategy my-strategy
      ]] ]
    ]
    [
      ask n-of (- diff) players [
        ask my-strategy [kill-yourself]
        die
      ]
      set n-of-trials min list n-of-trials (n-of-agents - ifelse-value self-matching? [0][1])
    ]
    ask players [
      set other-agents other players
    ]
    set n-of-revisions-per-tick min (list n-of-revisions-per-tick n-of-agents)
  ]
end

;;;;;;;;;;;;;;;
;;; PAYOFFS ;;;
;;;;;;;;;;;;;;;

to have-payoff-ready
  if not played? [
    run update-payoff
    set played? true
  ]
end

to update-counterparts-with-replacement
  set counterparts n-values n-of-trials [one-of [population-to-play-with] of my-player]
end

to update-counterparts-without-replacement
  set counterparts n-of n-of-trials [population-to-play-with] of my-player
end

to update-payoff-not-full-matching
  run update-counterparts
  play-vs-list-of-strategies [my-strategy] of counterparts
end

to update-payoff-full-matching
  play-vs-list-of-strategies [my-strategy] of population-to-play-with
end

;;;;;;;;;;;;;;;;;;;;;;;
;;; UPDATE-STRATEGY ;;;
;;;;;;;;;;;;;;;;;;;;;;;

to update-strategy
  ifelse random-float 1 < prob-mutation
    [
      set my-next-strategy new-random-strategy
    ]
    [run follow-rule]
end

to update-candidate-agents-and-payoffs
  set candidates (turtle-set
    my-strategy
    ([my-strategy] of (n-of n-to-consider-imitating other-agents))
  )
  ;; no replacement
  ;; note that candidates is an agentset to select from, and you are included in it.
  ask candidates [have-payoff-ready]
end

to update-candidate-strategies-and-payoffs
  set candidates (turtle-set
    my-strategy
    n-values (n-in-test-set - 1) [new-random-strategy]
  )
  ;; we will have to kill the strategies that we do not select
  update-payoffs-of-strategies candidates
end

to update-payoffs-of-strategies [strategy-set]
  ;; We assume clever payoff evaluation, i.e. to compute the payoff of a strategy
  ;; that the revising agent is not using, we imagine that the agent switches to this new strategy,
  ;; and then we compute the payoff of this new strategy in this new state.
  ;; Useful relevant notes in Sandholm (2010, "Population Games and Evolutionary Dynamics", section 11.4.2, pp. 419-421)

  let ag-strategy my-strategy

  ask my-strategy [run update-counterparts]

  ask strategy-set [
    set counterparts runresult reported-counterparts
    ;; reported-counterparts can be fixed-counterparts (if single-sample?)
    ;; or variable-counterparts (if not single-sample?)

    let candidate-strategy self
    ;; ask the agent to adopt this strategy, so payoffs are computed
    ;; under the hypothesis that the agent has switched (clever payoff evaluation).
    ;; This is also relevant if the agent himself is part of the set of counterparts.
    ask myself [set my-strategy candidate-strategy]
    play-vs-list-of-strategies [my-strategy] of counterparts
    ask myself [set my-strategy ag-strategy]
    ;; the line above must be within this ask because reported-counterparts takes the
    ;; counterparts of the agent's strategy

    ;; Note that the revising agent could be part of counterparts (if self-matching? is on).
    ;; This, together with clever payoff evaluation (see above), implies that even when using
    ;; single-sample? each strategy may be evaluated against a different set of sample strategies,
    ;; since the agent is switching strategy before evaluating payoffs.
  ]
end

;; POSSIBLE VALUES OF reported-counterparts

to-report fixed-counterparts
  report [counterparts] of ([my-strategy] of myself)
end

to-report variable-counterparts
  run update-counterparts
  report counterparts
end

;; DECISION-METHODS

to best
  run update-candidates-and-payoffs
  let best-candidates candidates with-max [payoff]
  set my-next-strategy new-strategy-copy-of (runresult tie-winner-in best-candidates)
  ask candidates with [my-player = myself] [if (self != [my-strategy] of myself) [kill-yourself]]
  ;; with [my-player = myself] is included for imitative protocols
end

to proportional
  ;; useful relevant notes in Sandholm (2010, "Population Games and Evolutionary Dynamics", section 4.3.1, pp. 126-127)

  if rate-scaling != 0 [
    ;; rate-scaling is zero only if the whole payoff matrix is 0s.
    ;; In that case there is nothing to do here.

    ifelse candidate-selection = "direct" [set n-in-test-set 2] [set n-to-consider-imitating 1]
    run update-candidates-and-payoffs

    let sorted-candidates sort-on [payoff] candidates

    let worse first sorted-candidates
    let better last sorted-candidates
    let payoff-diff ([payoff] of better - [payoff] of worse)

    if random-float 1 < (payoff-diff / rate-scaling) [
      set my-next-strategy new-strategy-copy-of better
    ]
    ;; If your strategy is the better, you are going to stick with it
    ;; If it's not, you switch with probability (payoff-diff / rate-scaling)

    ask candidates with [my-player = myself] [if (self != [my-strategy] of myself) [kill-yourself]]
    ;; with [my-player = myself] is included for imitative protocols
  ]
end

to logit
  run update-candidates-and-payoffs
  carefully [
    let chosen-candidate rnd:weighted-one-of candidates [ exp (payoff / eta)]
    set my-next-strategy new-strategy-copy-of chosen-candidate
    ask candidates with [my-player = myself] [if (self != [my-strategy] of myself) [kill-yourself]]
    ;; with [my-player = myself] is included for imitative protocols
  ]
  [
    user-message "Logit has computed a number that is too big for IEEE 754 floating-point computation\nPlease consider using a lower value for eta."
    print error-message
  ]
end


;; TIE-BREAKERS

to-report stick-uniform [st-agentset]
  report ifelse-value (member? my-strategy st-agentset) [my-strategy] [one-of st-agentset]
end

to-report uniform [st-agentset]
  report one-of st-agentset
end

;;;;;;;;;;;;;;
;;; GRAPHS ;;;
;;;;;;;;;;;;;;

to setup-graphs
  setup-miliseconds-graph "Matches with # number of CC outcomes (recent)" 1
  setup-graph "Matches with # number of CC outcomes (complete)" 1
  set-current-plot "Outcomes (complete)"
    set-current-plot-pen "DD"    set-plot-pen-interval plot-every-?-secs
    set-current-plot-pen "CD/DC" set-plot-pen-interval plot-every-?-secs
    set-current-plot-pen "CC"    set-plot-pen-interval plot-every-?-secs

  update-graphs
end

to setup-graph [s mode]
  set-current-plot s
  foreach possible-numbers-of-CCs [ [n] ->
    create-temporary-plot-pen (word n)
    set-plot-pen-mode mode
    set-plot-pen-interval plot-every-?-secs
    set-plot-pen-color color-for-n-of-CCs n
  ]
end

to setup-miliseconds-graph [s mode]
  set-current-plot s
  foreach possible-numbers-of-CCs [ [n] ->
    create-temporary-plot-pen (word n)
    set-plot-pen-mode mode
    set-plot-pen-interval 1000 * plot-every-?-secs
    set-plot-pen-color color-for-n-of-CCs n
  ]
end

to-report color-for-n-of-CCs [n]
  report ifelse-value (n < (n-of-rounds / 2))
    [scale-color red   n (- n-of-rounds / 2) (n-of-rounds / 2)]
    [scale-color green n (3 * n-of-rounds / 2) (n-of-rounds / 2)]
end

to update-n-of-outcomes
  ;; this procedure sets the payoffs of every strategy,
  ;; but not in a consistent way for every strategy.
  set n-of-CC-outcomes 0
  set n-of-DD-outcomes 0
  set n-of-outcomes 0
  set n-of-CC-outcomes-histogram n-values (n-of-rounds + 1) [0]

  let list-of-strategies [my-strategy] of players
  if self-matching? [
    foreach list-of-strategies [[s1] ->
      ask s1 [ play-vs-strategy s1 ]
    ]
  ]

  let l list-of-strategies
  foreach list-of-strategies [[s1] ->
    ask s1 [
      set l but-first l
      if length l > 1 [play-vs-list-of-strategies l]
    ]
  ]

end

to update-graphs

  if show-recent-history? or show-complete-history? [
    update-n-of-outcomes
    let total-n-of-matches (sum n-of-CC-outcomes-histogram)

    if show-recent-history? [
      set-current-plot "Matches with # number of CC outcomes (recent)"
        let bar total-n-of-matches
        foreach possible-numbers-of-CCs [ [n] ->
          set-current-plot-pen (word n)
          plotxy (1000 * second-to-plot) bar
          set bar (bar - (item n n-of-CC-outcomes-histogram))
        ]
        fix-x-range
        set-plot-y-range 0 total-n-of-matches
    ]

    if show-complete-history? [
      set-current-plot "Matches with # number of CC outcomes (complete)"
        let bar total-n-of-matches
        foreach possible-numbers-of-CCs [ [n] ->
          set-current-plot-pen (word n)
          plotxy second-to-plot bar
          set bar (bar - (item n n-of-CC-outcomes-histogram))
        ]
        set-plot-y-range 0 total-n-of-matches

      set-current-plot "Number of CC outcomes (complete)"
        set-current-plot-pen "min"  plotxy second-to-plot first-positive-position n-of-CC-outcomes-histogram
        set-current-plot-pen "max"  plotxy second-to-plot last-positive-position n-of-CC-outcomes-histogram
        set-current-plot-pen "avg"  plotxy second-to-plot (sum (map * possible-numbers-of-CCs n-of-CC-outcomes-histogram)) / total-n-of-matches

      set-current-plot "Outcomes (complete)"
        set-current-plot-pen "DD"    plotxy second-to-plot n-of-outcomes
        set-current-plot-pen "CD/DC" plotxy second-to-plot (n-of-outcomes - n-of-DD-outcomes)
        set-current-plot-pen "CC"    plotxy second-to-plot n-of-CC-outcomes
        set-plot-y-range 0 n-of-outcomes
    ]
  ]

  set second-to-plot (second-to-plot + plot-every-?-secs)
end

to fix-x-range
  set-plot-x-range floor (max (list 0 (1000 * (second-to-plot - duration-of-recent)))) floor (1000 * second-to-plot + (1000 * plot-every-?-secs))
end


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SUPPORTING PROCEDURES ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;
;;; Lists ;;;
;;;;;;;;;;;;;

to-report all-equal? [l]
  let first-element first l
  report reduce and (map [ [el] -> el = first-element] l)
end

to-report max-positions [numbers]
  let biggest max numbers
  report filter [ [n] -> item n numbers = biggest] (range (length numbers))
end

to-report subtract-one-in-pos-?1-of-list-?2 [pos l]
  report replace-item pos l ((item pos l) - 1)
end

to-report add-one-in-pos-?1-of-list-?2 [pos l]
  report replace-item pos l ((item pos l) + 1)
end

to-report first-positive-position [l]
  let positions-list filter [ [n] -> item n l > 0] (range (length l))
  report ifelse-value (length positions-list > 0) [first positions-list][false]
end

to-report last-positive-position [l]
  let positions-list filter [ [n] -> item n l > 0] (range (length l))
  report ifelse-value (length positions-list > 0) [last positions-list][false]
end


;;;;;;;;;;;;;;;;;;;;;
;; Parameter files ;;
;;;;;;;;;;;;;;;;;;;;;

to setup-list-of-parameters
  set list-of-parameters (list
    "CC-payoff"
    "CD-payoff"
    "DC-payoff"
    "DD-payoff"
    "n-of-rounds"
    "n-of-agents"
    "candidate-selection"
    "decision-method"
    "complete-matching?"
    "n-of-trials"
    "single-sample?"
    "n-in-test-set"
    "tie-breaker"
    "eta"
    "n-to-consider-imitating"
    "use-prob-revision?"
    "prob-revision"
    "n-of-revisions-per-tick"
    "prob-mutation"
    "trials-with-replacement?"
    "self-matching?"
    "plot-every-?-secs"
    "duration-of-recent"
    "show-recent-history?"
    "show-complete-history?"
    )
end

;; This procedure loads in data from a text file and sets the variables accordingly.
to load-parameter-file
  let file user-file

  ;; Note that we need to check that file isn't false. user-file
  ;; will return false if the user cancels the file dialog.
  if ( file != false )
  [
    ;; This opens the file, so we can use it.
    file-open file

    ;; Read in the file (assumed to be in exactly the same format as when saved )
    while [not file-at-end?]
    [
      let string file-read-line
      let comma-position position "," string
      let variable-name substring string 0 comma-position
      let value substring string (comma-position + 1) (length string)
      run (word "set " variable-name " " value)
    ]

    user-message "File loading complete!"

    ;; Done reading in the information.  Close the file.
    file-close

    startup
  ]

end

;; This procedure saves the parameters into a new file
;; or appends the data to an existing file
to save-parameter-file
  let file user-new-file

  if ( file != false )
  [
    carefully [file-delete file] [] ;; overwrite the file if it exists
    file-open file

    foreach list-of-parameters [ [p] -> file-print (word p "," (fix-string runresult p)) ]
    file-close
  ]
end

to-report fix-string [s]
  report ifelse-value is-string? s [ (word "\"" (remove "\n" s)  "\"") ] [s]
end

;;;;;;;;;;;;;;;;;;;;;;
;;; Random numbers ;;;
;;;;;;;;;;;;;;;;;;;;;;

;to-report cum-list-from [w]
;  let cum-list (list first w)
;  ;; cum-list first value is the first value of w, and it is as long as w
;  foreach but-first w [set cum-list lput (? + last cum-list) cum-list]
;  report cum-list
;end
;
;to-report rd-index-by-cumulative-weights [cw]
;  let rd-index 0
;  let tmp random-float last cw
;  ;; select the new strategy with probability proportional to the elements of i-d
;  foreach cw [ if (tmp > ?) [set rd-index (rd-index + 1)] ]
;  report rd-index
;end
;
;to-report rd-index-by-weights-from [w]
;  report rd-index-by-cumulative-weights (cum-list-from w)
;end

;; if speed is critical, consider using extension rnd (https://github.com/NetLogo/Rnd-Extension)
;; The extension uses Keith Schwarz's implementation of Vose's Alias Method (see http://www.keithschwarz.com/darts-dice-coins/).
;; Assuming you are choosing n candidates for a collection of size m with repeats, this method has an initialization cost of O(m),
;; followed by a cost of O(1) for each item you pick, so O(m + n) overall.
;; rnd:weighted-n-of-list-with-repeats implements

;; examples and speed comparisons in file random-sampling-weights.nlogo
@#$#@#$#@
GRAPHICS-WINDOW
15
663
1047
773
-1
-1
1.0
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
1023
-100
0
0
0
1
ticks
30.0

SLIDER
24
201
249
234
n-of-agents
n-of-agents
2
1000
100.0
1
1
NIL
HORIZONTAL

SLIDER
308
126
496
159
prob-revision
prob-revision
0.001
1
0.001
0.001
1
NIL
HORIZONTAL

SLIDER
517
362
668
395
prob-mutation
prob-mutation
0
1
0.001
0.001
1
NIL
HORIZONTAL

BUTTON
26
10
110
43
setup
startup
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
222
10
302
43
go once
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
121
10
210
43
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
678
10
798
55
NIL
ticks
17
1
11

SLIDER
301
270
496
303
duration-of-recent
duration-of-recent
1
100
10.0
1
1
sec.
HORIZONTAL

SWITCH
302
309
496
342
show-recent-history?
show-recent-history?
1
1
-1000

SWITCH
302
346
496
379
show-complete-history?
show-complete-history?
0
1
-1000

SWITCH
308
89
496
122
use-prob-revision?
use-prob-revision?
1
1
-1000

SLIDER
301
230
496
263
plot-every-?-secs
plot-every-?-secs
0.01
5
0.1
0.01
1
NIL
HORIZONTAL

SLIDER
309
163
496
196
n-of-revisions-per-tick
n-of-revisions-per-tick
1
n-of-agents
1.0
1
1
NIL
HORIZONTAL

MONITOR
809
10
930
55
NIL
ticks-per-second
3
1
11

SLIDER
782
148
965
181
n-of-trials
n-of-trials
1
10
1.0
1
1
NIL
HORIZONTAL

SLIDER
555
155
735
188
n-in-test-set
n-in-test-set
2
10
2.0
1
1
NIL
HORIZONTAL

TEXTBOX
679
346
734
364
for logit:
11
0.0
1

SLIDER
679
362
802
395
eta
eta
0.001
5
1.0
0.001
1
NIL
HORIZONTAL

CHOOSER
678
297
802
342
tie-breaker
tie-breaker
"stick-uniform" "uniform"
1

TEXTBOX
680
281
777
299
for best:
11
0.0
1

SLIDER
555
209
735
242
n-to-consider-imitating
n-to-consider-imitating
1
max-n-to-consider-imitating
1.0
1
1
NIL
HORIZONTAL

TEXTBOX
556
192
737
211
for imitative & (best or logit):
11
0.0
1

TEXTBOX
556
139
707
157
for direct & (best or logit):
11
0.0
1

CHOOSER
553
88
734
133
candidate-selection
candidate-selection
"imitative" "direct"
1

CHOOSER
517
289
668
334
decision-method
decision-method
"best" "logit" "proportional"
0

TEXTBOX
785
192
970
211
for direct protocols:
11
0.0
1

SWITCH
783
209
964
242
single-sample?
single-sample?
1
1
-1000

SWITCH
33
379
239
412
trials-with-replacement?
trials-with-replacement?
1
1
-1000

SWITCH
33
343
239
376
self-matching?
self-matching?
0
1
-1000

PLOT
22
424
369
651
Matches with # number of CC outcomes (recent)
milliseconds
NIL
0.0
1.0
0.0
0.0
true
true
"" ""
PENS

PLOT
374
424
733
651
Matches with # number of CC outcomes (complete)
seconds
NIL
0.0
1.0
0.0
0.0
true
true
"" ""
PENS

BUTTON
330
10
490
43
load parameters from file
load-parameter-file
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
500
10
647
43
save parameters to file
save-parameter-file
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

TEXTBOX
287
67
529
99
Assignment of revision opportunities
13
13.0
1

TEXTBOX
835
68
908
86
Matching
13
13.0
1

TEXTBOX
574
67
724
85
Candidate selection
13
13.0
1

TEXTBOX
517
346
667
364
mutations:
11
0.0
1

TEXTBOX
611
261
741
279
Decision method
13
13.0
1

TEXTBOX
66
65
216
83
Game and population
13
13.0
1

TEXTBOX
341
210
459
228
Plotting of output
12
0.0
1

TEXTBOX
67
320
220
338
Secondary parameters\n
12
0.0
1

SLIDER
24
89
134
122
CC-payoff
CC-payoff
0
10
3.0
1
1
NIL
HORIZONTAL

SLIDER
137
89
247
122
CD-payoff
CD-payoff
0
10
0.0
1
1
NIL
HORIZONTAL

SLIDER
24
126
134
159
DC-payoff
DC-payoff
0
10
4.0
1
1
NIL
HORIZONTAL

SLIDER
138
126
248
159
DD-payoff
DD-payoff
0
10
1.0
1
1
NIL
HORIZONTAL

SLIDER
24
165
248
198
n-of-rounds
n-of-rounds
1
16
3.0
1
1
NIL
HORIZONTAL

PLOT
810
262
1045
415
Number of CC outcomes (complete)
seconds
NIL
0.0
1.0
0.0
0.0
true
true
"" ""
PENS
"max" 1.0 0 -13840069 true "" ""
"avg" 1.0 0 -16777216 true "" ""
"min" 1.0 0 -2674135 true "" ""

PLOT
735
424
1046
651
Outcomes (complete)
NIL
NIL
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"DD" 1.0 1 -2674135 true "" ""
"CD/DC" 1.0 1 -1 true "" ""
"CC" 1.0 1 -13840069 true "" ""

BUTTON
302
384
496
417
NIL
draw one-of strategies
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SWITCH
782
89
966
122
complete-matching?
complete-matching?
1
1
-1000

TEXTBOX
782
132
966
150
for complete-matching = off
11
0.0
1

CHOOSER
34
243
239
288
initial-condition
initial-condition
"random" "TFT"
1

@#$#@#$#@
## WHAT IS IT?

(a general understanding of what the model is trying to show or explain)

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)
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
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

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

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.0.1
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
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
