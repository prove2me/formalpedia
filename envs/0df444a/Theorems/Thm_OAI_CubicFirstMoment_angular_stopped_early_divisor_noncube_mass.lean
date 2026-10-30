-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_stopped_early_divisor_noncube_mass
-- name    : OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:56:04.584786+00:00
-- url     : https://prove2.me/theorems/c03deda0-5a77-4a2e-90ec-ecd4a9b59e26
-- title:
--   OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedEarlyDivisorMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedEarlyDivisorMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_stopped_early_divisor_noncube_mass
--       (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
--       (ℓ : ℤ) (hℓ : ℓ ≠ 0)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       {ξ κ H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
--       (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) (k : ℕ) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
--         1 ≤ l → X^κ ≤ b → b ≤ X →
--         0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
--         1 ≤ B → B ≤ b^(3/5:ℝ) →
--         ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
--         (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
--         ∀ (S U : Finset Eisenstein),
--         (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
--         (∀ p ∈ U, primaryPrime p) →
--         ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
--         ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
--         2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
--         2*(Real.log X)^(2*(4*(k+2)+k)) ≤
--           min (X^ξ) (geometricBinLower (1+δ) X h) →
--         angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
--           (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
--             j₀ k₀ h Z Q early) e S U ≤
--           K*b^2*B^(1/3:ℝ)/(Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.geometricBinLower` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.angularStoppedDivisorMass`, `OAI.CubicFirstMoment.geometricPrimeBin` and `OAI.CubicFirstMoment.stoppedSideTest` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primaryPrime` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_stopped_noncube_radial_form` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularStoppedEarlyDivisorMass.lean (declaration OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass)

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
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_early_divisor_noncube_mass
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S U : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ p ∈ U, primaryPrime p) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) e S U ≤
        K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
