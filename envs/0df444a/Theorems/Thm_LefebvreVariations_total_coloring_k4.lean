-- Prove2me | Theorems.Thm_LefebvreVariations_total_coloring_k4
-- name    : LefebvreVariations.total_coloring_k4
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:13:12.057247+00:00
-- url     : https://prove2.me/theorems/5ebdad1e-7ff3-51cb-b5df-4bdbe3c2cbbb
-- title:
--   Lefebvre's variations, No. 173 — on a theme by Vizing: the complete graph K_4 has a total colouring with at most maximum degree plus 2 colours
-- statement:
--   $$\chi''(K_4)\ \le\ \Delta(K_4)+2 = 5 .$$
--
--   $K_4$ has $4$ vertices and $6$ edges, so $10$ elements to colour, and needs $5$ colours but no more. The total colouring conjecture asserts $\chi''(G)\le\Delta(G)+2$ for every graph; for $\Delta\le3$ it is a theorem, and this is the smallest instance with $\chi''=\Delta+2$ exactly.
--
--   **Formalization Note** The statement is the conclusion of `total_coloring_conjecture` for the graph `G` on `Fin 4` determined by the stated adjacency (a hypothesis `hG`, so that any decidable instance can be used): there are `k ≤ G.maxDegree + 2`, vertex colours, edge colours, with adjacent vertices, adjacent edges and incident vertex-edge pairs all coloured differently.
--
--   **Why this is a variation.** This is a variation of the open total colouring conjecture (platform problem total_coloring_conjecture), instantiated in the parent's own formulation (k <= maxDegree + 2, colours on vertices and on edges) at a fixed graph. It is a first non-trivial size: a Type 2 graph, where the bound Delta + 2 is attained, so a prover must exhibit an explicit 5-colouring of 10 elements. No formal link to the general conjecture is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   V. G. Vizing (1964) and M. Behzad (1965) for the conjecture; Rosenfeld (1971) and Vijayaditya (1971) prove chi'' <= 5 for maximum degree 3, Kostochka for maximum degree 4 and 5 (checked via search against the literature; years cited from memory). The total chromatic number of this graph being 5 was verified here by exhaustive search (a 5-colouring exists, no 4-colouring).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Total colouring conjecture (Vizing, Behzad) for the complete graph `K_4`, in the parent's formulation `k ≤ Δ + 2` with `Δ = 3`. `K_4` is the smallest graph whose total chromatic number is exactly `Δ + 2 = 5` (Type 2): a total colouring with 5 colours exists, none with 4. Existence of a 5-colouring was verified by exhaustive search.
Source: Vizing (1964) and Behzad (1965) for the conjecture; `chi''(K_n) = n` for odd `n` and `n + 1` for even `n` is classical (cited from memory). -/
theorem total_coloring_k4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (hG : ∀ a b : Fin 4, G.Adj a b ↔ a ≠ b) :
    ∃ (k : ℕ) (cV : Fin 4 → Fin k) (cE : G.edgeSet → Fin k),
      k ≤ G.maxDegree + 2 ∧
      (∀ v w : Fin 4, G.Adj v w → cV v ≠ cV w) ∧
      (∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ → (∃ v, v ∈ e₁.val ∧ v ∈ e₂.val) → cE e₁ ≠ cE e₂) ∧
      (∀ v : Fin 4, ∀ e : G.edgeSet, v ∈ e.val → cV v ≠ cE e) := by
  sorry

end LefebvreVariations
