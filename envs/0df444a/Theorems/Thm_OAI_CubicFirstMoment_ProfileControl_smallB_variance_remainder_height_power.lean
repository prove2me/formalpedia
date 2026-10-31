-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_ProfileControl_smallB_variance_remainder_height_power
-- name    : OAI.CubicFirstMoment.ProfileControl.smallB_variance_remainder_height_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:13:53.950967+00:00
-- url     : https://prove2.me/theorems/de4ee423-82c8-4f01-8e9d-38cca872397e
-- title:
--   OAI.CubicFirstMoment.ProfileControl.smallB_variance_remainder_height_power: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.ProfileControl.smallB_variance_remainder_height_power` of [lean/OAI/NumberTheory/CubicMoment/Estimates/ProfileVarianceRemainder.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/ProfileVarianceRemainder.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment.ProfileControl`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem smallB_variance_remainder_height_power
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       :
--       ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
--         (Z A T u : ℝ), 65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
--         (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
--         dyadicHeightMean (fun t =>
--           ‖smoothedDispersionVariance S β (u+t) P.V A-varianceZeroMode S β P.V A‖) T ≤
--           (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.dyadicHeightMean` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PoissonProfileBudget` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.smoothedDispersionVariance` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.varianceZeroMode` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.localized_integral_power_saving` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/ProfileVarianceRemainder.lean (declaration OAI.CubicFirstMoment.ProfileControl.smallB_variance_remainder_height_power)

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
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem smallB_variance_remainder_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t) P.V A-varianceZeroMode S β P.V A‖) T ≤
        (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  sorry

end CubicFirstMoment.ProfileControl

end

end OAI
end
