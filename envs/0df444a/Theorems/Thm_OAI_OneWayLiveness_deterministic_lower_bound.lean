-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_deterministic_lower_bound
-- name    : OAI.OneWayLiveness.deterministic_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:29:58.00332+00:00
-- url     : https://prove2.me/theorems/9ba1e31f-99d3-4ce9-b08e-ff997c834350
-- title:
--   Exponential state lower bound for two-way deterministic automata recognising one-way liveness
-- statement:
--   Fix $h\ge 2$ and let $[h]=\{0,\dots,h-1\}$. The alphabet $\Sigma_h$ consists of all binary relations on $[h]$, and the one-way liveness language is
--
--   $$\mathrm{OWL}_h=\bigl\{R_1\cdots R_n\in\Sigma_h^{*}:\ R_1R_2\cdots R_n\neq\varnothing\bigr\},$$
--
--   where $R_1R_2\cdots R_n$ is the relational product in diagrammatic order; so a word is live exactly when there are $x_0,\dots,x_n\in[h]$ with $(x_{k-1},x_k)\in R_k$ for all $k$ (for the empty word the product is the identity relation, which is nonempty).
--
--   A word $w=a_1\cdots a_n$ is read by a two-way automaton on the tape $\vdash a_1\cdots a_n\dashv$ with cells $0,1,\dots,n+1$: cell $0$ holds the left endmarker $\vdash$, cell $k$ ($1\le k\le n$) holds $a_k$, and cell $n+1$ holds the right endmarker $\dashv$. A configuration is a pair $(k,q)$ of a head position $k\in\{0,\dots,n+1\}$ and a state $q$; a step from $(k,q)$ applies a transition for the symbol in cell $k$, which specifies a new state and a move of the head by $-1$, $0$ or $+1$. A two-way deterministic automaton $D$ with $s$ states has state set $\{0,\dots,s-1\}$, an initial state $q_0$, a set of accepting states, and a partial transition function assigning to some pairs (state, symbol) a new state and a move, where the head never moves left from $\vdash$ nor right from $\dashv$. Two acceptance conventions are used: under the positive convention the automaton accepts $w$ if some configuration with an accepting state is reachable from the start configuration $(0,q_0)$, where $q_0$ is the initial state, by a run of at least one step; under the reflexive convention runs of zero steps are also allowed. No halting or end-of-tape condition is imposed. $D$ recognises $\mathrm{OWL}_h$ under a convention if it accepts exactly the words of $\mathrm{OWL}_h$.
--
--   If $D$ has $s$ states and recognises $\mathrm{OWL}_h$ under the positive convention, respectively the reflexive convention, then
--
--   $$2^{\lfloor (h-2)/31\rfloor}\le 4\,(s+\delta)^2,\qquad \delta=\begin{cases}2&\text{(positive convention)},\\ 1&\text{(reflexive convention)}.\end{cases}$$
--
--   Consequently the number of states grows exponentially in $h$: $s+\delta\ge 2^{\lfloor (h-2)/31\rfloor/2-1}$. Together with the one-way nondeterministic automaton with $h+3$ states for the same language, this gives an exponential gap between nondeterministic one-way and deterministic two-way state complexity for this family of languages.
--
--   **Formalization Note** The automaton is `D : DMachine (Alphabet h) s` with `Alphabet h = BRel (Fin h)`, the language is `OWL h`, and recognition is `D.Recognizes positive (OWL h)`; the run relation `FiniteRun positive` is the transitive closure of the step relation for `positive = true` and its reflexive-transitive closure otherwise. The exponent uses natural-number subtraction and division.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Recognition.lean#L78-L95

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

open OAI OAI.OneWayLiveness

theorem OAI.OneWayLiveness.deterministic_lower_bound (h : ℕ) (hh : 2 ≤ h) (positive : Bool) (s : ℕ)
    (D : DMachine (Alphabet h) s) (hD : D.Recognizes positive (OWL h)) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1)^2 := by sorry
