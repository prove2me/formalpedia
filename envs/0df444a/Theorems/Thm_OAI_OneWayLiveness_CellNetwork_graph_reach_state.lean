-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_CellNetwork_graph_reach_state
-- name    : OAI.OneWayLiveness.CellNetwork.graph_reach_state
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:15:33.762579+00:00
-- url     : https://prove2.me/theorems/4fc9809f-9116-462b-a24a-9e371a2a0450
-- title:
--   Reachability between state vertices of the cell network equals reachability of configurations
-- statement:
--   Let $M$ be a deterministic two-way automaton with state set $Q$, let $f\in Q$ be a distinguished state, and let $w$ be an input word. A configuration is a pair $c=(i,p)$ of a cell $i\in\{0,\dots,|w|+1\}$ of the endmarked tape and a state $p$, and $c\vdash_M c'$ denotes one computation step of $M$ on $w$. Let $G=G_{M,f,w}$ be the cell network of $M$ on $w$. It is a functional graph with a state vertex $\langle c\rangle$ for every configuration $c$, and its edges leaving state vertices are exactly the computation steps of $M$.
--
--   **Theorem.** For all configurations $c,c'$ of $M$ on $w$,
--   $$
--   \langle c\rangle\to^{*}\langle c'\rangle\ \text{ in } G\quad\Longleftrightarrow\quad c\vdash_M^{*}c' .
--   $$
--   Here $\to^{*}$ is reachability along directed edges of $G$ (paths of length $\ge0$), and $\vdash_M^{*}$ is the reflexive–transitive closure of the step relation of $M$ on $w$.
--
--   Thus the cell network is a faithful model of the computation of $M$ on $w$. In particular, the question whether $M$ gets from $(0,q_0)$ to $(|w|+1,f)$ becomes a reachability question in a graph that is assembled cell by cell from local pieces depending only on the scanned symbols. This is how acceptance is later detected by boundary colorings of the cell diagrams.
--
--   **Formalization Note** Reachability in the graph is `(graph M finish w).Reach`, the reflexive–transitive closure of its step relation. The right-hand side is `Relation.ReflTransGen (M.Step w) c c'`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Network.lean#L356-L373

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.CellNetwork
variable (Q : Type)
variable {Q} {Alpha : Type} (M : Machine Alpha Q)
variable (Q)
variable {Q}

theorem OAI.OneWayLiveness.CellNetwork.graph_reach_state (finish : Q) (w : List Alpha) (c c' : Machine.Config (Q := Q) w) :
    (graph M finish w).Reach (stateVertex w c) (stateVertex w c') ↔
      Relation.ReflTransGen (M.Step w) c c' := by sorry
