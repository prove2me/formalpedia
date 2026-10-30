-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_ProfileControl_smallB_common_sum_height_power
-- name    : OAI.CubicFirstMoment.ProfileControl.smallB_common_sum_height_power
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:52:06.205394+00:00
-- url     : https://prove2.me/theorems/e7e76a2b-5e8d-46ca-a290-e19e175d035e
-- title:
--   OAI.CubicFirstMoment.ProfileControl.smallB_common_sum_height_power: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.ProfileControl.smallB_common_sum_height_power` of [lean/OAI/NumberTheory/CubicMoment/Estimates/ProfileCommonSmall.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/ProfileCommonSmall.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment.ProfileControl`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem smallB_common_sum_height_power
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       :
--       ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S I : Finset Eisenstein) (β : Eisenstein → ℂ)
--         (Z A T u : ℝ), 0 < Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
--         I ⊆ commonRowFactors S →
--         (∀ k ∈ I, 4 ≤ (⌊Z/norm k⌋₊:ℝ) ∧ 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ)) →
--         (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
--         dyadicHeightMean (fun t => ‖∑ k ∈ I, commonGramBlock S
--           (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k‖) T ≤
--         (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.dyadicHeightMean` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.commonRowFactors` and `OAI.CubicFirstMoment.dispersionAmplitude` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PoissonProfileBudget` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.commonGramBlock` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.ProfileControl.smallB_variance_remainder_height_power` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/ProfileCommonSmall.lean (declaration OAI.CubicFirstMoment.ProfileControl.smallB_common_sum_height_power)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem smallB_common_sum_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S I : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 0 < Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      I ⊆ commonRowFactors S →
      (∀ k ∈ I, 4 ≤ (⌊Z/norm k⌋₊:ℝ) ∧ 16 ≤ (⌊Z/norm k⌋₊:ℝ)^(3/4:ℝ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t => ‖∑ k ∈ I, commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k‖) T ≤
      (K*P.cost)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  sorry

end CubicFirstMoment.ProfileControl

end

end OAI
end
