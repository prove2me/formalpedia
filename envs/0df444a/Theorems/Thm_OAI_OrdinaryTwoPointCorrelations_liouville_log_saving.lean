-- Prove2me | Theorems.Thm_OAI_OrdinaryTwoPointCorrelations_liouville_log_saving
-- name    : OAI.OrdinaryTwoPointCorrelations.liouville_log_saving
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-07T04:32:59.307259+00:00
-- url     : https://prove2.me/theorems/9e7e90b6-b6fe-4562-9a53-9e3a02bc82f9
-- statement:
--   The theorem states that there is an absolute constant c > 0 such that, for all natural numbers a₁, a₂, b₁, b₂ with a₁ > 0, a₂ > 0 and a₁b₂ ≠ a₂b₁ (so the two affine forms a₁n+b₁ and a₂n+b₂ are not proportional), there exists a constant C > 0, which may depend on a₁, a₂, b₁, b₂ but not on X, such that for every real X ≥ 3 the affine correlation sum of the Liouville function with itself is small. Here the Liouville function λ is the complex-valued version of the arithmetic function n ↦ (−1)^Ω(n), and the affine sum is Σ_{n=1}^{⌊X⌋} λ(a₁n+b₁) λ(a₂n+b₂). The claimed bound is that its complex absolute value is at most C·X / (log X)^c, a power-of-the-logarithm saving over the trivial bound of size X. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean; bytes 1409..1751
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_OrdinaryTwoPointCorrelations

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate

open Filter

namespace OrdinaryTwoPointCorrelations

open TwoPointCorrelations

theorem liouville_log_saving :
    ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ,
      0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
      ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
        ‖affineSum liouville liouville a₁ a₂ b₁ b₂ ⌊X⌋₊‖ ≤
          C * X / Real.rpow (Real.log X) c := by
  sorry

end OrdinaryTwoPointCorrelations
end
end OAI
