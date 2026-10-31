-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_localized_integral_power_saving
-- name    : OAI.CubicFirstMoment.localized_integral_power_saving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:01:21.564205+00:00
-- url     : https://prove2.me/theorems/154d4702-169d-48fc-9d4f-490201f079e5
-- title:
--   OAI.CubicFirstMoment.localized_integral_power_saving: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.localized_integral_power_saving` of [lean/OAI/NumberTheory/CubicMoment/Estimates/LocalizedNormalized.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/LocalizedNormalized.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem localized_integral_power_saving
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve) :
--       ∃ (γ K Z₀ : ℝ), 0 < γ ∧ 0 < K ∧
--         ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T M : ℝ),
--         Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → 0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
--         (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
--         (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
--         ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
--         Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
--         (∀ t, ‖h t‖ ≤ M) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
--         (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ M) →
--         (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
--         ‖heightBilinearValue P S α β h X₀ T‖ ≤
--           K*M*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*γ/3))*
--             Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` and `OAI.CubicFirstMoment.dyadicHeightSupport` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.heightBilinearValue` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_angular_tailPrime_high_group_uniform`, `OAI.CubicFirstMoment.angular_tailPrime_upper_group_bound_uniform`, `OAI.CubicFirstMoment.angular_upperStoppedFilteredTail_isLittleO_uniform`, `OAI_CubicFirstMoment_angular_upperStoppedTail_bound_uniform`, `OAI_CubicFirstMoment_tailPrime_high_group_uniform`, `OAI.CubicFirstMoment.tailPrime_upper_group_bound_uniform`, `OAI.CubicFirstMoment.upperStoppedFilteredTail_isLittleO_uniform` and `OAI_CubicFirstMoment_upperStoppedTail_bound_uniform` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/LocalizedNormalized.lean (declaration OAI.CubicFirstMoment.localized_integral_power_saving)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A010

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace CubicFirstMoment

theorem localized_integral_power_saving
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (γ K Z₀ : ℝ), 0 < γ ∧ 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T M : ℝ),
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → 0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖h t‖ ≤ M) → (∀ t, t ∉ dyadicHeightSupport T → h t = 0) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ M) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖heightBilinearValue P S α β h X₀ T‖ ≤
        K*M*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*γ/3))*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  sorry

end CubicFirstMoment

end

end OAI
end
