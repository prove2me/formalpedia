-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_Machine_positiveCopy_accepts
-- name    : OAI.OneWayLiveness.Machine.positiveCopy_accepts
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:13:12.371477+00:00
-- url     : https://prove2.me/theorems/f9517e75-5628-4a44-ae46-41b56fac0775
-- title:
--   A fresh copy of the initial state converts positive-run acceptance into reflexive acceptance
-- statement:
--   Let $M$ be a deterministic two-way automaton over an alphabet $\Sigma$ with an arbitrary state set $Q$, initial state $q_0$, accepting set $F\subseteq Q$ and partial transition function $\delta$. On an input $w=w_1\cdots w_n$ it runs on the tape $\triangleright w_1\cdots w_n\triangleleft$ with positions $0,\dots,n+1$, and a configuration is a pair (position, state). The *positive copy* $M^{+}$ has state set $Q\cup\{\star\}$ with a fresh initial state $\star$. Its accepting set is $F$, so $\star$ is not accepting. Its transitions are $\delta^{+}(q,b)=\delta(q,b)$ for $q\in Q$ and $\delta^{+}(\star,b)=\delta(q_0,b)$: the fresh state copies the transition row of $q_0$.
--
--   **Theorem.** For every word $w\in\Sigma^{*}$,
--   $$
--   M^{+}\ \text{accepts } w \text{ by a run of length}\ \ge 0\quad\Longleftrightarrow\quad M\ \text{accepts } w \text{ by a run of length}\ \ge 1 .
--   $$
--   That is, $M^{+}$ has a run, possibly of length zero, from $(0,\star)$ to a configuration with an accepting state iff $M$ has a run of at least one step from $(0,q_0)$ to a configuration with an accepting state.
--
--   The positive acceptance convention forbids accepting by the empty computation. The copy makes the initial configuration non-accepting while keeping all behaviour after the first step. As a result, any bound proved for automata with reflexive acceptance applies to positive acceptance at the cost of one extra state; in the deterministic lower bound this is the source of the term $s+2$ in place of $s+1$.
--
--   **Formalization Note** $M^{+}$ is `M.positiveCopy`, with state type `Option Q` and `none` playing the role of $\star$. `Accepts false` uses the reflexive–transitive closure of the step relation and `Accepts true` its transitive closure (`FiniteRun`). No finiteness of $Q$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Normalization.lean#L95-L114

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.Machine
variable {Alpha Q : Type} (M : Machine Alpha Q)

theorem OAI.OneWayLiveness.Machine.positiveCopy_accepts (w : List Alpha) :
    M.positiveCopy.Accepts false w ↔ M.Accepts true w := by sorry
