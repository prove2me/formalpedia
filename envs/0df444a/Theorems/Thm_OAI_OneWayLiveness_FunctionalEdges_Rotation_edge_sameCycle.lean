-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_FunctionalEdges_Rotation_edge_sameCycle
-- name    : OAI.OneWayLiveness.FunctionalEdges.Rotation.edge_sameCycle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:12:00.435158+00:00
-- url     : https://prove2.me/theorems/43f7fe82-21c7-4191-a20d-7317c9a75853
-- title:
--   Both darts of an edge leading to a terminal vertex lie on the same tour of a rotation system
-- statement:
--   Let $G$ be a *functional edge structure*. It consists of a set $V$ of vertices, a set $E$ of edges, and source and target maps $\mathrm{src},\mathrm{dst}:E\to V$, where $\mathrm{src}$ is injective. Thus every vertex has at most one outgoing edge; loops and parallel edges are allowed. Write $v\to w$ if some edge goes from $v$ to $w$, and $\to^{*}$ for the reflexive–transitive closure of $\to$.
--
--   Each edge $e$ has two darts: $(e,0)$ at the vertex $\mathrm{src}(e)$ and $(e,1)$ at the vertex $\mathrm{dst}(e)$. The flip $\mathrm{fl}(e,\epsilon)=(e,\neg\epsilon)$ exchanges them. A *rotation* is a permutation $\pi$ of the darts that keeps every dart at its vertex and whose cycles are exactly the sets of darts at a common vertex. Its *tour* permutation is
--   $$
--   T=\pi\circ\mathrm{fl},
--   $$
--   which crosses the current edge and then turns at the endpoint.
--
--   **Theorem.** Assume $E$ is finite. Let $t\in V$ be a terminal vertex, meaning that $\mathrm{src}(e)\neq t$ for every edge $e$, and let $e$ be an edge with $\mathrm{src}(e)\to^{*}t$. Then the two darts of $e$ lie in the same cycle of $T$:
--   $$
--   \exists\,k\in\mathbb{Z}:\qquad T^{k}(e,0)=(e,1).
--   $$
--
--   View $G$ with its rotation as a ribbon graph. The cycles of $T$ are then its boundary walks, and the theorem says that both darts of an edge in the basin of a terminal vertex are visited by the same boundary walk. Combined with the fact that all darts at one vertex lie on a common tour, this shows that the whole basin of a terminal vertex lies on a single tour. In the cell network of a two-way automaton, this single tour forces equal boundary colors at the two test ports whenever the automaton reaches its final configuration.
--
--   **Formalization Note** The structure is `FunctionalEdges V E`, darts are `E × Bool`, and a rotation is `G.Rotation`, a `CyclicOrder` of the dart-to-vertex map. The tour is `R.tour = R.perm * G.flip`, reachability is `G.Reach` (the reflexive–transitive closure of `G.Step`), and the conclusion is `R.tour.SameCycle (e, false) (e, true)`. $V$ is arbitrary; only $E$ is assumed finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Tours.lean#L150-L168

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.FunctionalEdges OAI.OneWayLiveness.FunctionalEdges.Rotation
variable {V E : Type*} (G : FunctionalEdges V E)
variable {G} (R : G.Rotation)

theorem OAI.OneWayLiveness.FunctionalEdges.Rotation.edge_sameCycle [Finite E] {t : V} (ht : ∀ e, G.src e ≠ t) (e : E)
    (h : G.Reach (G.src e) t) : R.tour.SameCycle (e, false) (e, true) := by sorry
