-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_CellNetwork_graph_step_from_state
-- name    : OAI.OneWayLiveness.CellNetwork.graph_step_from_state
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:14:42.182948+00:00
-- url     : https://prove2.me/theorems/f7c6b9ec-e305-4bf6-9dd1-9ba138c88d62
-- title:
--   Edges leaving state vertices of the cell network are exactly the automaton's steps
-- statement:
--   Let $M$ be a deterministic two-way automaton with state set $Q$ and partial transition function $\delta$, let $f\in Q$ be a distinguished state, and let $w=w_1\cdots w_n$ be an input. The input is read on the tape $b_0b_1\cdots b_{n+1}=\triangleright w_1\cdots w_n\triangleleft$. A configuration is a pair $c=(i,p)$ of a cell $i\in\{0,\dots,n+1\}$ and a state $p$. We write $(i,p)\vdash_M(i',p')$ if $\delta(p,b_i)=(p',d)$ and $i'=i-1$, $i$ or $i+1$ according as $d$ is a left, stay or right move.
--
--   The *cell network* $G=G_{M,f,w}$ from the cell-network definitions is a functional graph: every vertex has at most one outgoing edge. Its vertices include a *state vertex* $\langle i,p\rangle$ for every configuration, together with auxiliary dummy vertices and outer leaves. It has one edge for every *candidate move*:
--   - for each pair of adjacent cells and each slot $(d,p,q)$, a crossing edge, going rightward from cell $j$ to $j+1$ or leftward from $j+1$ to $j$;
--   - for each cell and each pair $(p,q)$, a stay edge;
--   - an outward edge from each outer leaf into an endmarker cell.
--
--   A candidate move into state $q$ ends at the state vertex of $q$ in its destination cell. It starts at the state vertex $\langle i,p\rangle$ of its source cell if $\delta(p,b_i)$ is exactly that move, and at a private dummy vertex otherwise.
--
--   **Theorem.** For every configuration $c$ and every vertex $v$ of $G$,
--   $$
--   \langle c\rangle\to v\ \text{ in } G\quad\Longleftrightarrow\quad v=\langle c'\rangle\ \text{ for some configuration } c'\ \text{with}\ c\vdash_M c' .
--   $$
--   Here $\langle c\rangle\to v$ means that some edge of $G$ has source $\langle c\rangle$ and target $v$.
--
--   The edge set of the network is the same for every automaton with state set $Q$; only the attachment of sources depends on $\delta$. The theorem says that the edges leaving state vertices encode exactly the computation steps of $M$ on $w$. It is the basis for translating reachability of configurations into reachability in the network.
--
--   **Formalization Note** The graph is `graph M finish w : FunctionalEdges (Vertex Q w.length) (Edge Q w.length)`, with step relation `FunctionalEdges.Step` and state vertices `stateVertex w c`. The automaton's step relation is `M.Step w c c'`. No finiteness of $Q$ is needed. The parameter $f$ (`finish`) affects only the targets of the outward edges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Network.lean#L291-L354

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

theorem OAI.OneWayLiveness.CellNetwork.graph_step_from_state (finish : Q) (w : List Alpha) (c : Machine.Config (Q := Q) w)
    (v : Vertex Q w.length) :
    (graph M finish w).Step (stateVertex w c) v ↔
      ∃ c', v = stateVertex w c' ∧ M.Step w c c' := by sorry
