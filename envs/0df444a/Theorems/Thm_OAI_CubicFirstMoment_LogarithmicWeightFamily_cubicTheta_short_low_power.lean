-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_LogarithmicWeightFamily_cubicTheta_short_low_power
-- name    : OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_short_low_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:14:01.157324+00:00
-- url     : https://prove2.me/theorems/32816648-31ec-41a6-a88e-d29ad987ea53
-- title:
--   OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_short_low_power: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_short_low_power` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaShortModelLow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaShortModelLow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter MeasureTheory`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem LogarithmicWeightFamily.cubicTheta_short_low_power
--       {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
--       (ℓ : ℤ) (hℓ : ℓ ≠ 0)
--       {D : ℝ} (hD : 0 ≤ D) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
--         (α : Eisenstein → ℂ) (X R U C : ℝ),
--         2 ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → 0 ≤ C → C ≤ X →
--         R^(3/2:ℝ)*C^(3/2:ℝ) ≤ X^(159/200:ℝ) →
--         (∀ r ∈ S, primary r ∧ Squarefree r ∧ norm r ≤ 2*R) →
--         (∀ r ∈ S, Y (w r) = X) →
--         (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
--         ‖∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C‖ ≤
--           K*X^(41/50:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.metaplecticShortCompletionError` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_logarithmic_typeI_corrected_mixed_actual`, `OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual`, `OAI_CubicFirstMoment_angular_typeI_low_proved`, `OAI.CubicFirstMoment.logarithmic_prime_typeI_mixed_full_actual`, `OAI.CubicFirstMoment.short_outer_low_bound_actual` and `OAI.CubicFirstMoment.stopped_typeI_mixed_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaShortModelLow.lean (declaration OAI.CubicFirstMoment.LogarithmicWeightFamily.cubicTheta_short_low_power)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
local notation "κ" => (1/10000:ℝ)

theorem LogarithmicWeightFamily.cubicTheta_short_low_power
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U C : ℝ),
      2 ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → 0 ≤ C → C ≤ X →
      R^(3/2:ℝ)*C^(3/2:ℝ) ≤ X^(159/200:ℝ) →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∑ r ∈ S, ‖α r‖) ≤ D*R*X^κ →
      ‖∑ r ∈ S, α r*metaplecticShortCompletionError r ℓ (W (w r)) U C‖ ≤
        K*X^(41/50:ℝ) := by
  sorry

end CubicFirstMoment

end

end OAI
end
