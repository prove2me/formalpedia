-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_PathNFA_accepts_iff
-- name    : OAI.OneWayLiveness.PathNFA.accepts_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:33:16.16653+00:00
-- url     : https://prove2.me/theorems/0d8de7df-e477-4d17-a95e-ac201863e2f4
-- title:
--   The path automaton accepts exactly the live words under both acceptance conventions
-- statement:
--   A word $w=a_1\cdots a_n$ is read by a two-way automaton on the tape $\vdash a_1\cdots a_n\dashv$ with cells $0,1,\dots,n+1$: cell $0$ holds the left endmarker $\vdash$, cell $k$ ($1\le k\le n$) holds $a_k$, and cell $n+1$ holds the right endmarker $\dashv$. A configuration is a pair $(k,q)$ of a head position $k\in\{0,\dots,n+1\}$ and a state $q$; a step from $(k,q)$ applies a transition for the symbol in cell $k$, which specifies a new state and a move of the head by $-1$, $0$ or $+1$. Two acceptance conventions are used: under the positive convention the automaton accepts $w$ if some configuration with an accepting state is reachable from the start configuration $(0,q_0)$, where $q_0$ is the initial state, by a run of at least one step; under the reflexive convention runs of zero steps are also allowed. No halting or end-of-tape condition is imposed.
--
--   Let $H$ be an arbitrary set and consider words $w=R_1\cdots R_n$ over the alphabet $\mathcal R_H$ of all binary relations on $H$. Products of relations are compositions in diagrammatic order ($(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$), the empty product being the identity relation $\Delta_H$. The path automaton $N_H$ is the nondeterministic two-way automaton with states $\mathsf{start}$, a path state $\langle p\rangle$ for each $p\in H$, an accepting state $\mathsf{acc}$ and an unused state $\mathsf{rej}$, initial state $\mathsf{start}$ and accepting set $\{\mathsf{acc}\}$, whose only transitions are:
--   1. in $\mathsf{start}$ reading $\vdash$: move right and enter any $\langle p\rangle$, $p\in H$;
--   2. in $\langle p\rangle$ reading a letter $R$: move right and enter any $\langle q\rangle$ with $(p,q)\in R$;
--   3. in $\langle p\rangle$ reading $\dashv$: stay and enter $\mathsf{acc}$.
--
--   Then for both acceptance conventions and every word $w=R_1\cdots R_n$ over $\mathcal R_H$,
--
--   $$N_H\ \text{accepts}\ w\iff R_1R_2\cdots R_n\neq\varnothing,$$
--
--   that is, iff there are $x_0,\dots,x_n\in H$ with $(x_{k-1},x_k)\in R_k$ for all $k$. For $H=[h]$ this is a one-way (the head never moves left) nondeterministic automaton with $h+3$ states for the one-way liveness language, which is the upper-bound half of the separation between nondeterministic one-way and deterministic two-way automata for this language.
--
--   **Formalization Note** The automaton is `PathNFA.machine : NMachineOn (BRel H) (Option (H ⊕ Bool))`, an automaton on an arbitrary state type; the statement is `machine.Accepts positive w ↔ BRel.live w` for `positive : Bool`. No finiteness of $H$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/PathNFA.lean#L192-L237

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.PathNFA
variable {H : Type}

theorem OAI.OneWayLiveness.PathNFA.accepts_iff (positive : Bool) (w : List (BRel H)) :
    machine.Accepts positive w ↔ BRel.live w := by sorry
