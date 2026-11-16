-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_Supplement_lemma_6_2
-- name    : MinCostArbPacking.Main.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:47:33.318607+00:00
-- url     : https://prove2.me/theorems/725288c7-2fa3-4227-829e-41c8b2ed53b6
-- title:
--   Lemma 6.2 — two-stage greedy inclusion
-- statement:
--   Let G be any finite undirected multigraph, k≥1, and fix any strict total order on its edge set E. Let P^k be unions of k pseudoforests and G^k be unions of k forests. Run all three greedy scans with that same order, setting
--
--   $$\Pi=\operatorname{Greedy}_{P^k}(E),\quad\Phi=\operatorname{Greedy}_{\mathcal G^k}(\Pi),\quad B=\operatorname{Greedy}_{\mathcal G^k}(E).$$
--
--   Then Φ⊆B. The order is arbitrary and need not arise from costs. The assertion includes empty graphs, loops and parallel edges. This supports Theorem 1.2 by identifying edges that may be retained and contracted without losing the direct greedy optimum.
--
--   Differences from the source:
--   - encoding: a finite directed or undirected multigraph → the published edge-identity multigraph with vertices Fin n and edges Fin m; reason: finite relabelling preserves loops, parallel edges, isolated vertices and all original competing subsets; in the undirected case endpoint order is ignored by forest independence
--   - encoding: an arbitrary common strict total order on E → one permutation enumerating all edge identities used in all three scans; reason: every strict total order on a finite edge set has exactly such an enumeration
--   - encoding: a pseudoforest has at most one cycle per connected component → each component has at most as many selected edges as vertices, and k-fold independence is an actual disjoint partition into such sets; reason: these are equivalent for finite multigraphs, including loops and parallel pairs; no abstract matroid compatibility is assumed
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Lemma 6.2, p. 29

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Supplement_Pseudoforest
set_option autoImplicit false

namespace MinCostArbPacking.Main.Supplement

/-- Lemma 6.2 (Two-stage greedy), p.29. All three scans use the same arbitrary strict total
order on the edge identities, encoded by its increasing enumeration ord. -/
theorem lemma_6_2 {n m : ℕ} (G : Digraph (Fin n) (Fin m)) (k : ℕ) (hk : 1 ≤ k)
    (ord : Equiv.Perm (Fin m)) :
    let piSet := greedy (PseudoIndepK G k) ord Finset.univ
    let Φ := greedy (G.IndepK k) ord piSet
    let B := greedy (G.IndepK k) ord Finset.univ
    Φ ⊆ B := by sorry

end MinCostArbPacking.Main.Supplement
