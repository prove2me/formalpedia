-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_stopped_divisor_noncube_total
-- name    : OAI.CubicFirstMoment.angular_stopped_divisor_noncube_total
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:21:02.177226+00:00
-- url     : https://prove2.me/theorems/fb49d1d2-e989-4826-be69-0b1e9d42cb52
-- title:
--   OAI.CubicFirstMoment.angular_stopped_divisor_noncube_total: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_stopped_divisor_noncube_total` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedDivisorTotal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedDivisorTotal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Set Filter MeasureTheory`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_stopped_divisor_noncube_total
--       (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
--       (ℓ : ℤ) (hℓ : ℓ ≠ 0)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
--       (hF : 0 ≤ F) (hJ : 0 ≤ J)
--       (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
--       (hΦ' : ContDiff ℝ ∞ Φ) (k H : ℕ) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
--         2 ≤ b → X^κ ≤ b → b ≤ X →
--         0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
--         ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
--         (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
--         b^(3/2:ℝ) ≤ A →
--         ∀ (d : Eisenstein) (hd : d ≠ 0), norm d ≤ b^(1/1000:ℝ) →
--         ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
--         ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
--         2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
--         2*(Real.log X)^(2*(4*(k+2)+k)) ≤
--           min (X^ξ) (geometricBinLower (1+δ) X h) →
--         ‖divisorNoncubePoissonContribution d hd (stoppedIntervalSupport ι X (b/2) b e)
--           (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
--             (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
--               j₀ k₀ h Z Q early)) u Φ A‖ ≤
--           K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` and `OAI.CubicFirstMoment.geometricBinLower` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.angularStoppedRowCoefficient`, `OAI.CubicFirstMoment.geometricPrimeBin`, `OAI.CubicFirstMoment.stoppedIntervalSupport` and `OAI.CubicFirstMoment.stoppedSideTest` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.divisorNoncubePoissonContribution` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_angular_stopped_divisor_full_model_log_saving` and `OAI.CubicFirstMoment.angular_stopped_sieved_model_log_saving` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedDivisorTotal.lean (declaration OAI.CubicFirstMoment.angular_stopped_divisor_noncube_total)

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
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_divisor_noncube_total
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A →
      ∀ (d : Eisenstein) (hd : d ≠ 0), norm d ≤ b^(1/1000:ℝ) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ‖divisorNoncubePoissonContribution d hd (stoppedIntervalSupport ι X (b/2) b e)
        (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early)) u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
