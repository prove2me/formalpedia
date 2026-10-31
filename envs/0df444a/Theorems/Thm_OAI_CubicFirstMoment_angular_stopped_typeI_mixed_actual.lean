-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_stopped_typeI_mixed_actual
-- name    : OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:21:28.20936+00:00
-- url     : https://prove2.me/theorems/dced2b61-33f6-42b0-b115-6c30436656f6
-- title:
--   OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularStoppedMixedTypeI.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularStoppedMixedTypeI.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem angular_stopped_typeI_mixed_actual (ℓ : ℤ)
--       {γ : Type*} {V : γ → ℝ → ℂ} (hVw : UniformLogWeights V)
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
--       {B ξ : ℝ} (hB : 1 ≤ B) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
--         ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
--           (w : Eisenstein → γ) (b A u : ℝ),
--         2 ≤ b → b ≤ X → 1 ≤ A → 2 ≤ (b/2)*A → B ≤ (b/2)*A →
--         b/2 ≤ ((b/2)*A)^(51/100:ℝ) →
--         (∀ r ∈ stoppedIntervalSupport ι X (b/2) b e,
--           ∀ x : ℝ, B < x → V (w r) x = 0) →
--         ‖∑ r ∈ stoppedIntervalSupport ι X (b/2) b e,
--           angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected r*
--             (typeIMixedGauss r (V (w r)) A-typeIMixedModel r (V (w r)) A)‖ ≤
--           K*A^(-1/6:ℝ)*((b/2)*A)^(5/6-1/100:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.angularStoppedRowCoefficient` and `OAI.CubicFirstMoment.stoppedIntervalSupport` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.typeIMixedGauss` and `OAI.CubicFirstMoment.typeIMixedModel` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_stopped_corrected_dispersion_log_saving_actual` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularStoppedMixedTypeI.lean (declaration OAI.CubicFirstMoment.angular_stopped_typeI_mixed_actual)

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
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_typeI_mixed_actual (ℓ : ℤ)
    {γ : Type*} {V : γ → ℝ → ℂ} (hVw : UniformLogWeights V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B ξ : ℝ} (hB : 1 ≤ B) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
        (w : Eisenstein → γ) (b A u : ℝ),
      2 ≤ b → b ≤ X → 1 ≤ A → 2 ≤ (b/2)*A → B ≤ (b/2)*A →
      b/2 ≤ ((b/2)*A)^(51/100:ℝ) →
      (∀ r ∈ stoppedIntervalSupport ι X (b/2) b e,
        ∀ x : ℝ, B < x → V (w r) x = 0) →
      ‖∑ r ∈ stoppedIntervalSupport ι X (b/2) b e,
        angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected r*
          (typeIMixedGauss r (V (w r)) A-typeIMixedModel r (V (w r)) A)‖ ≤
        K*A^(-1/6:ℝ)*((b/2)*A)^(5/6-1/100:ℝ) := by
  sorry

end CubicFirstMoment

end

end OAI
end
