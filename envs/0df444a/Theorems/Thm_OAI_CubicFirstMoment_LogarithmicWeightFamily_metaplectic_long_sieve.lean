-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_sieve
-- name    : OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:11:33.923275+00:00
-- url     : https://prove2.me/theorems/cd7014ef-097a-42ca-b0af-7ad3a52787f8
-- title:
--   OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve` of [lean/OAI/NumberTheory/CubicMoment/Transform/MetaplecticLongSieve.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Transform/MetaplecticLongSieve.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem LogarithmicWeightFamily.metaplectic_long_sieve
--       {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
--       (hW : LogarithmicWeightFamily Y W) {ε s : ℝ}
--       (hε : 0 < ε) (hεsmall : ε ≤ 1) (hs : 0 < s) :
--       ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein)
--         (X N U B C F : ℝ), 1 ≤ X → 1 ≤ N → 0 < U → 0 ≤ B →
--         0 < C → 1 ≤ F → B*U ≤ F →
--         (∀ r ∈ A, primary r ∧ norm r ≤ N) →
--         (∀ r ∈ A, Y (w r) ≤ X) →
--         (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
--         ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
--         ‖∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W (w r)) U C F‖^2 ≤
--           K*((metaplecticLongDyads C F).card:ℝ)^2*X^(2*s)*(N*(B*U))^ε*(B*U)*F^(4*ε)*
--             (N+8*B*U/C^3+(8*N*B*U/C^3)^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.metaplecticLongCompletion` and `OAI.CubicFirstMoment.metaplecticLongDyads` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual`, `OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual`, `OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual`, `OAI.CubicFirstMoment.short_outer_low_bound_actual` and `OAI.CubicFirstMoment.stopped_typeI_mixed_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Transform/MetaplecticLongSieve.lean (declaration OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem LogarithmicWeightFamily.metaplectic_long_sieve
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (hW : LogarithmicWeightFamily Y W) {ε s : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein)
      (X N U B C F : ℝ), 1 ≤ X → 1 ≤ N → 0 < U → 0 ≤ B →
      0 < C → 1 ≤ F → B*U ≤ F →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, Y (w r) ≤ X) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ r ∈ A, α r*metaplecticLongCompletion r ℓ (W (w r)) U C F‖^2 ≤
        K*((metaplecticLongDyads C F).card:ℝ)^2*X^(2*s)*(N*(B*U))^ε*(B*U)*F^(4*ε)*
          (N+8*B*U/C^3+(8*N*B*U/C^3)^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) := by
  sorry

end CubicFirstMoment

end

end OAI
end
