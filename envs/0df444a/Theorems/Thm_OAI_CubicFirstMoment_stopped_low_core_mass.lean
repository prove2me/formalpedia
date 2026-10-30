-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_stopped_low_core_mass
-- name    : OAI.CubicFirstMoment.stopped_low_core_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:29:28.076806+00:00
-- url     : https://prove2.me/theorems/ab93893e-d764-464a-a67a-a73190969c00
-- title:
--   OAI.CubicFirstMoment.stopped_low_core_mass: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.stopped_low_core_mass` of [lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedLowCoreMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedLowCoreMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem stopped_low_core_mass (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
--       {ξ κ H E F J d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
--       (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
--       (a k : ℕ) (ha : 0 < a) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (δ l b u V C : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
--         1 ≤ l → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
--         0 ≤ C → C ≤ X^d →
--         ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
--         (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
--         ∀ (S : Finset Eisenstein), S ⊆ lowNoncubeSupport ((Real.log X)^a) C →
--         ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
--         ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
--         (∑ v ∈ S, ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W
--           (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
--             j₀ k₀ h Z Q early) v e‖^2) ≤ K*C*b^2/(Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.geometricBinLower` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.KummerPrimeSiegelWalfisz` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.geometricPrimeBin` and `OAI.CubicFirstMoment.stoppedSideTest` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.lowNoncubeSupport` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.stoppedCharacterSum` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.stopped_early_divisor_noncube_mass` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Decomposition/StoppedLowCoreMass.lean (declaration OAI.CubicFirstMoment.stopped_low_core_mass)

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
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_low_core_mass (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {ξ κ H E F J d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (a k : ℕ) (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V C : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      0 ≤ C → C ≤ X^d →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S : Finset Eisenstein), S ⊆ lowNoncubeSupport ((Real.log X)^a) C →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
      (∑ v ∈ S, ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤ K*C*b^2/(Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
