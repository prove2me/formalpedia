-- Prove2me | Theorems.Thm_LefebvreVariations_total_coloring_k33
-- name    : LefebvreVariations.total_coloring_k33
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:13:30.710333+00:00
-- url     : https://prove2.me/theorems/5e6c0e13-9174-4f72-b6c5-5fb5e0b134d0
-- title:
--   Lefebvre's variations, No. 174 — on a theme by Vizing: the complete bipartite graph K_{3,3} has a total colouring with at most maximum degree plus 2 colours
-- statement:
--   $$\chi''(K_{3,3})\ \le\ \Delta(K_{3,3})+2 = 5 .$$
--
--   $K_{3,3}$ has $6$ vertices and $9$ edges, so $15$ elements, and needs $5$ colours. The total colouring conjecture asserts $\chi''(G)\le\Delta(G)+2$ for every graph; for $\Delta\le3$ it is a theorem, and this is the smallest instance with $\chi''=\Delta+2$ exactly.
--
--   **Formalization Note** The statement is the conclusion of `total_coloring_conjecture` for the graph `G` on `Fin 6 (parts {0,1,2} and {3,4,5})` determined by the stated adjacency (a hypothesis `hG`, so that any decidable instance can be used): there are `k ≤ G.maxDegree + 2`, vertex colours, edge colours, with adjacent vertices, adjacent edges and incident vertex-edge pairs all coloured differently.
--
--   **Why this is a variation.** This is a variation of the open total colouring conjecture (platform problem total_coloring_conjecture), instantiated in the parent's own formulation (k <= maxDegree + 2, colours on vertices and on edges) at a fixed graph. It is a first non-trivial size: a Type 2 graph, where the bound Delta + 2 is attained, so a prover must exhibit an explicit 5-colouring of 15 elements. No formal link to the general conjecture is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   V. G. Vizing (1964) and M. Behzad (1965) for the conjecture; Rosenfeld (1971) and Vijayaditya (1971) prove chi'' <= 5 for maximum degree 3, Kostochka for maximum degree 4 and 5 (checked via search against the literature; years cited from memory). The total chromatic number of this graph being 5 was verified here by exhaustive search (a 5-colouring exists, no 4-colouring).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Total colouring conjecture for the complete bipartite graph `K_{3,3}` (parts `{0,1,2}`, `{3,4,5}`), formulated with `k ≤ Δ + 2`, `Δ = 3`. `K_{3,3}` has total chromatic number `5 = Δ + 2` (Type 2); a total 5-colouring exists and none with 4 colours. Verified by exhaustive search. The conjecture is known for all graphs with `Δ ≤ 5` (Rosenfeld 1971, Vijayaditya 1971 for `Δ ≤ 3`; Kostochka for `Δ ≤ 5`) (cited from memory). -/
theorem total_coloring_k33 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hG : ∀ a b : Fin 6, G.Adj a b ↔ (a.val < 3 ∧ 3 ≤ b.val) ∨ (b.val < 3 ∧ 3 ≤ a.val)) :
    ∃ (k : ℕ) (cV : Fin 6 → Fin k) (cE : G.edgeSet → Fin k),
      k ≤ G.maxDegree + 2 ∧
      (∀ v w : Fin 6, G.Adj v w → cV v ≠ cV w) ∧
      (∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ → (∃ v, v ∈ e₁.val ∧ v ∈ e₂.val) → cE e₁ ≠ cE e₂) ∧
      (∀ v : Fin 6, ∀ e : G.edgeSet, v ∈ e.val → cV v ≠ cE e) := by
  sorry

end LefebvreVariations
