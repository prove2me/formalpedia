-- Prove2me | Theorems.Thm_OAI_Problem367_free_ising_factor_iff_threshold
-- name    : OAI.Problem367.free_ising_factor_iff_threshold
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:11.59156+00:00
-- url     : https://prove2.me/theorems/a612dbab-8633-4eaa-b80f-29dcf8a13a97
-- statement:
--   The theorem states that, for every natural number d ≥ 3 and every real β ≥ 0, a certain property of θ = tanh β holds if and only if tanh β ≤ 1/√(d−1). The property, IsFactorOfIID(d, θ), concerns the d-regular tree whose vertices are the reduced words over the alphabet {0,…,d−1} (finite words in which no two consecutive letters are equal), with two words adjacent when one is obtained from the other by appending a single letter. It asserts that there exists a measurable map Φ from i.i.d. labels in [0,1], one for each tree vertex under the product of uniform measures, to ±1 spin configurations on the vertices, satisfying two conditions. First, the pushforward law of Φ is the free Ising law with parameter θ: for every finite connected vertex set D and every spin assignment η on D, the probability that the spins on D equal η is (1/2)·∏ over edges {u,v} of D of (1+θ·s)/2, where s = +1 if η(u)=η(v) and s = −1 otherwise. Second, Φ is equivariant under every automorphism g of the tree: for almost every label configuration U, applying Φ to the relabelled configuration gives the same result as relabelling Φ(U) by g.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FreeIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FreeIsing.lean; bytes 2809..3011
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FreeIsing

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem free_ising_factor_iff_threshold :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta → (IsFactorOfIID d (Real.tanh beta) ↔ Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) := by
  sorry

end Problem367
end
end OAI
