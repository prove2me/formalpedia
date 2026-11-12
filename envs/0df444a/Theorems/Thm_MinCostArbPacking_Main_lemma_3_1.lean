-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_3_1
-- name    : MinCostArbPacking.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:30.904119+00:00
-- url     : https://prove2.me/theorems/176bd1b7-e2fc-4c69-a56d-9e86e78d3291
-- title:
--   Lemma 3.1 — $k$-arborescence packings are the $\mathcal G^k$-independent sets with indegree $k$ off the root
-- statement:
--   **Lemma 3.1 (Matroid formulation; Edmonds).** Let $G$ be a directed multigraph, $r$ a vertex and $k\ge1$ an integer. An arc set $I\subseteq E$ is the arc set of $k$ arc-disjoint $r$-arborescences if and only if
--
--   $$I\in\mathcal G^k,\qquad \deg^{in}_I(r)=0,\qquad \deg^{in}_I(v)=k\ \text{ for every } v\ne r.$$
--
--   It translates the packing problem into an intersection of the $k$-fold graphic matroid with the indegree partition matroid, which is the basis of the whole algorithm.
--
--   Differences from the source:
--   - generalization: graphs from which loops and arcs entering $r$ have been deleted (§3.1) → arbitrary finite multigraphs (loops and arcs entering $r$ allowed); reason: the statement remains true without the deletion, and the deleted graph is a special case
--   - encoding: vertices $V$ and arcs $E$ of the input multigraph → arbitrary finite types `V`, `E` with `tail head : E → V`; reason: every finite multigraph is of this form up to relabelling; parallel arcs are distinct elements
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.2, p.7, Lemma 3.1

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Graph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 3.1 (Edmonds), p.7: `I` is the arc set of `k` arc-disjoint `r`-arborescences iff `I` is
independent in `𝒢^k`, no arc of `I` enters `r`, and every other vertex has indegree `k` in `I`. -/
theorem lemma_3_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (r : V) (k : ℕ) (hk : 1 ≤ k) (I : Finset E) :
    (∃ P : Fin k → Finset E, G.IsPacking r k P ∧ I = Finset.univ.biUnion P) ↔
      (G.IndepK k I ∧ G.inDeg I r = 0 ∧ ∀ v, v ≠ r → G.inDeg I v = k) := by sorry

end MinCostArbPacking.Main
