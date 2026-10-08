-- Prove2me | Theorems.Thm_OAI_CompactBanach_main
-- name    : OAI.CompactBanach.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:27.343732+00:00
-- url     : https://prove2.me/theorems/c937bfb2-0c76-4c91-b574-831abacb85b4
-- statement:
--   The theorem states that there is a natural number Λ such that for every real Banach space B (a complete normed real vector space, in universe u) that is not finite-dimensional, there is a compact subset K of B that is doubling with constant at most Λ and does not bi-Lipschitz embed into any finite-dimensional real normed space E (in universe v). Doubling at most Λ means that for every point x of K and every radius r>0, the points of K at distance less than r from x can be covered by at most Λ points of K, called centers, such that every such point lies at distance less than r/2 from some center. Admitting a bi-Lipschitz embedding into E means there is a map f from K to E, a constant a>0 and a constant D≥1 with a·d(x,y) ≤ d(f(x),f(y)) ≤ D·a·d(x,y) for all x,y in K. The theorem asserts that no such f exists for any finite-dimensional E, with Λ independent of B.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CompactBanach.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CompactBanach.lean; bytes 978..1328
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CompactBanach

namespace OAI

universe u v

namespace CompactBanach

theorem main : ∃ Λ : ℕ, ∀ (B : Type u) [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B], ¬ FiniteDimensional ℝ B →
    ∃ K : Set B, IsCompact K ∧ DoublingAtMost K Λ ∧
      ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E], ¬ AdmitsBiLipschitzEmbedding K E := by
  sorry

end CompactBanach
end OAI
