-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_ProfileControl_smallB_poisson_annulus_height_power
-- name    : OAI.CubicFirstMoment.ProfileControl.smallB_poisson_annulus_height_power
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:12:21.611639+00:00
-- url     : https://prove2.me/theorems/600aeebf-e007-438a-a134-94518d085c8d
-- title:
--   OAI.CubicFirstMoment.ProfileControl.smallB_poisson_annulus_height_power: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.ProfileControl.smallB_poisson_annulus_height_power` of [lean/OAI/NumberTheory/CubicMoment/Estimates/ProfilePoissonAnnulus.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/ProfilePoissonAnnulus.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment.ProfileControl`, with `open Set`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem smallB_poisson_annulus_height_power
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve) (q : ℕ) (hq : q ≤ 3) :
--       ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
--         (Z : ℕ) (A B T u N J : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
--         (Z:ℝ)^(1/50:ℝ) ≤ T → 0 < A → 0 < N → 0 < J →
--         (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
--         (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) 2) →
--         8*B ≤ (Z:ℝ)^(3/4:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
--         (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
--         (1+A*J/(27*N^2))^q*dyadicHeightMean (fun t =>
--           ‖finitePoissonContribution S H β (u+t) P.V A‖) T ≤
--           (K*P.cost)*(A/N)*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.dyadicHeightMean` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PoissonProfileBudget` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.finitePoissonContribution` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.ProfileControl.smallB_common_sum_height_power` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/ProfilePoissonAnnulus.lean (declaration OAI.CubicFirstMoment.ProfileControl.smallB_poisson_annulus_height_power)

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
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem smallB_poisson_annulus_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (q : ℕ) (hq : q ≤ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (A B T u N J : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 < A → 0 < N → 0 < J →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, norm b/N ∈ Icc (1:ℝ) 2) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
      (1+A*J/(27*N^2))^q*dyadicHeightMean (fun t =>
        ‖finitePoissonContribution S H β (u+t) P.V A‖) T ≤
        (K*P.cost)*(A/N)*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  sorry

end CubicFirstMoment.ProfileControl

end

end OAI
end
