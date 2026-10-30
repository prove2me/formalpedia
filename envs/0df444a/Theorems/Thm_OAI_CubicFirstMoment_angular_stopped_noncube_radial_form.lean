-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_stopped_noncube_radial_form
-- name    : OAI.CubicFirstMoment.angular_stopped_noncube_radial_form
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:56:50.012+00:00
-- url     : https://prove2.me/theorems/6310d488-819a-489f-9cc7-90268643e779
-- title:
--   OAI.CubicFirstMoment.angular_stopped_noncube_radial_form: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_stopped_noncube_radial_form` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedRadialForm.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedRadialForm.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Set Filter MeasureTheory`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_stopped_noncube_radial_form
--       (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
--       (ℓ : ℤ) (hℓ : ℓ ≠ 0)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
--       (hF : 0 ≤ F) (hJ : 0 ≤ J)
--       (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
--       (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (δ b u V B Y : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
--         2 ≤ b → X^κ ≤ b → b ≤ X →
--         0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
--         1 ≤ B → B ≤ b^(3/5:ℝ) →
--         ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
--         (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
--         0 < Y → ∀ (S : Finset Eisenstein) (phase : Eisenstein → ℂ),
--         (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
--         (∀ v ∈ S, Y ≤ norm v ∧ norm v ≤ 2*Y) → (∀ v ∈ S, ‖phase v‖ ≤ 1) →
--         ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
--         ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
--         2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
--         2*(Real.log X)^(2*(4*(k+2)+k)) ≤
--           min (X^ξ) (geometricBinLower (1+δ) X h) →
--         ∀ ρ : ℝ, 0 ≤ ρ →
--         (1+ρ)^q*‖normCoprimeRadialForm (stoppedIntervalSupport ι X (b/2) b e) S
--           (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W
--             (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
--               j₀ k₀ h Z Q early) n))
--           (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W
--             (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
--               j₀ k₀ h Z Q early) n))
--           phase (fun v => norm v/Y) (fun n => norm n/(b/2)) Φ ρ‖ ≤
--         K*b^2*B^(1/3:ℝ)/(Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.MontgomeryVaughanBound` and `OAI.CubicFirstMoment.geometricBinLower` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.angularStoppedRowCoefficient`, `OAI.CubicFirstMoment.geometricPrimeBin`, `OAI.CubicFirstMoment.stoppedIntervalSupport` and `OAI.CubicFirstMoment.stoppedSideTest` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.normCoprimeRadialForm` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_stopped_divisor_noncube_total` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedRadialForm.lean (declaration OAI.CubicFirstMoment.angular_stopped_noncube_radial_form)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008
import Definitions.Def_OAIQ096A010

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

theorem angular_stopped_noncube_radial_form
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V B Y : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      0 < Y → ∀ (S : Finset Eisenstein) (phase : Eisenstein → ℂ),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ v ∈ S, Y ≤ norm v ∧ norm v ≤ 2*Y) → (∀ v ∈ S, ‖phase v‖ ≤ 1) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*‖normCoprimeRadialForm (stoppedIntervalSupport ι X (b/2) b e) S
        (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) n))
        (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) n))
        phase (fun v => norm v/Y) (fun n => norm n/(b/2)) Φ ρ‖ ≤
      K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
