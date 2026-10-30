-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_low_far_logCell_integrated_bound
-- name    : OAI.CubicFirstMoment.low_far_logCell_integrated_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:26:41.836842+00:00
-- url     : https://prove2.me/theorems/106d7473-0a93-427a-ba87-4da3606e88ae
-- title:
--   OAI.CubicFirstMoment.low_far_logCell_integrated_bound: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.low_far_logCell_integrated_bound` of [lean/OAI/NumberTheory/CubicMoment/Estimates/LowFarHeight.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/LowFarHeight.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory`, `open scoped BigOperators FourierTransform`):
--
--   ```lean
--   theorem low_far_logCell_integrated_bound
--       (hpnt : PrimaryPrimePNT)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve) :
--       ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
--         ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
--           (α β : Eisenstein → ℂ) (Z A X₀ T M H : ℝ),
--         (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ →
--         (1+Real.log Z)^Ct ≤ T → 0 ≤ M → 0 ≤ H →
--         (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
--         (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
--         (∀ b ∈ S, ‖β b‖ ≤ M) →
--         ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
--         Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
--         (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ H) →
--         (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
--         ‖(T:ℂ)⁻¹*∑ e ∈ farLogNormCells P S J A (Z/2) X₀,
--           logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤
--         K*(J/T)^2*H*(J*Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*
--           Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
--           J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
--             Real.sqrt (∑ a ∈ P, ‖α a‖^2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` and `OAI.CubicFirstMoment.dyadicHeightSupport` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.farLogNormCells` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.logCellHeightSum` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.low_localized_height_integral_bound` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/LowFarHeight.lean (declaration OAI.CubicFirstMoment.low_far_logCell_integrated_bound)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

theorem low_far_logCell_integrated_bound
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A X₀ T M H : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → 0 < X₀ →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ M → 0 ≤ H →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      ∀ h : ℝ → ℂ, Integrable h → Differentiable ℝ h → Integrable (deriv h) →
      Differentiable ℝ (deriv h) → Integrable (deriv (deriv h)) →
      (∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ H) →
      (∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0) →
      ‖(T:ℂ)⁻¹*∑ e ∈ farLogNormCells P S J A (Z/2) X₀,
        logCellHeightSum P S α β J A (Z/2) X₀ e h‖ ≤
      K*(J/T)^2*H*(J*Real.sqrt (A/J)*Real.sqrt (∑ a ∈ P, ‖α a‖^2)*
        Real.sqrt (∑ b ∈ S, ‖β b‖^2)+
        J^2*Real.sqrt (J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)) := by
  sorry

end CubicFirstMoment

end

end OAI
end
