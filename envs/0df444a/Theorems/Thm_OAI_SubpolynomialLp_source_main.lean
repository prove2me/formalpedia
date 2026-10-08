-- Prove2me | Theorems.Thm_OAI_SubpolynomialLp_source_main
-- name    : OAI.SubpolynomialLp.source_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:27.344434+00:00
-- url     : https://prove2.me/theorems/800a3f07-53cd-415c-a465-6050b5bba594
-- statement:
--   The theorem states that, for a real exponent p>1 with p≠2, three claims hold about d_p(n,D), the least dimension d such that every injective n-tuple x in an L^p space (over any measure space in universe u) admits a bi-Lipschitz-type embedding into (ℝ^d, ℓ^p): there exist points y_i in ℝ^d and a scale s>0 with s‖x_i−x_j‖ ≤ (Σ_a |y_i(a)−y_j(a)|^p)^{1/p} ≤ D·s·‖x_i−x_j‖ for all i,j. This least dimension is defined as an infimum over natural numbers, so the theorem also asserts that it itself has this property. First, for every real D>1 there is a constant C such that for all n≥2 the dimension d_p(n,D) has the embedding property, is at least log n / log(1+2D), and is at most exp(C·(log n)^γ), where γ=2−p if p<2 and γ=1−2/p if p>2. Second, for every n≥9 with D=1 (exact distortion bound), d_p(n,1) has the embedding property and satisfies ⌊(n−1)/4⌋² ≤ d_p(n,1) ≤ n(n−1)/2, with the floor division and subtraction taken in natural numbers. Third, for every real D≥1, log d_p(n,D)/log n tends to 0 as n→∞ when D>1, and to 2 when D=1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SubpolynomialLp.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SubpolynomialLp.lean; bytes 1082..1878
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SubpolynomialLp

namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Topology

universe u

namespace SubpolynomialLp

/-- The universal coordinate dimension bounds and their logarithmic limits. -/
theorem source_main (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) :
    (∀ D : ℝ, 1 < D → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      GoodDimension.{u} p n D (dimension.{u} p n D) ∧
      Real.log (n : ℝ) / Real.log (1 + 2 * D) ≤ (dimension.{u} p n D : ℝ) ∧
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C * Real.log (n : ℝ) ^ gamma p)) ∧
    (∀ n : ℕ, 9 ≤ n →
      GoodDimension.{u} p n 1 (dimension.{u} p n 1) ∧
      ((n - 1) / 4) ^ 2 ≤ dimension.{u} p n 1 ∧
      dimension.{u} p n 1 ≤ n.choose 2) ∧
    (∀ D : ℝ, 1 ≤ D →
      Tendsto (fun n : ℕ => Real.log (dimension.{u} p n D : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (if 1 < D then 0 else 2))) := by
  sorry

end SubpolynomialLp
end
end OAI
