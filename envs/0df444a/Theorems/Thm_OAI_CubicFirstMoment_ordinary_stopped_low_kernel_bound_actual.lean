-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_ordinary_stopped_low_kernel_bound_actual
-- name    : OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:27:36.008447+00:00
-- url     : https://prove2.me/theorems/4a0be4c1-f624-4d01-904c-d3ef0aa85055
-- title:
--   OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralStoppedOrdinaryLowSaving.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralStoppedOrdinaryLowSaving.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem ordinary_stopped_low_kernel_bound_actual (i : ℕ)
--       (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
--       {C ξ ρ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
--       (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (k Ct : ℕ) :
--       ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (N : ℕ) (d : Fin i → Fin N) (A b H : ℝ),
--         X/16 ≤ A*b → A*b ≤ 16*X →
--         X^(7/20:ℝ) ≤ b → b ≤ X^(39/100:ℝ) → 0 < H →
--         ∀ (j q h : ℕ) (Z Q : ℝ) (early : Bool), j ≤ h →
--         2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower ρ X h) →
--         ∀ (E₀ U P : Finset Eisenstein) (remaining : Eisenstein → Prop),
--         (∀ e ∈ E₀, primary e) →
--         (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
--         let S := stoppedIntervalSupport (Fin i) X (b/2) b 1
--         let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
--           (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j q h Z Q early)
--         ‖∑ a ∈ P, ∑ b ∈ S, stoppedAlpha E₀ U primeDetectorCutoff (X^ξ) remaining a*β b*
--           centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b)‖ ≤
--           K*X^(5/6:ℝ)/(Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound`, `OAI.CubicFirstMoment.geometricBinLower`, `OAI.CubicFirstMoment.primeDetectorCutoff` and `OAI.CubicFirstMoment.primeProductEnvelope` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.distinguishedStoppingWeights` (definitions bundle `OAIQ096A006` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.KummerPrimeSiegelWalfisz` and `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.geometricPrimeBin`, `OAI.CubicFirstMoment.stoppedAlpha`, `OAI.CubicFirstMoment.stoppedIntervalSupport`, `OAI.CubicFirstMoment.stoppedRowCoefficient` and `OAI.CubicFirstMoment.stoppedSideTest` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.centeredHeightKernel` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralStoppedOrdinaryLowSaving.lean (declaration OAI.CubicFirstMoment.ordinary_stopped_low_kernel_bound_actual)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

theorem ordinary_stopped_low_kernel_bound_actual (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C ξ ρ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (k Ct : ℕ) :
    ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (N : ℕ) (d : Fin i → Fin N) (A b H : ℝ),
      X/16 ≤ A*b → A*b ≤ 16*X →
      X^(7/20:ℝ) ≤ b → b ≤ X^(39/100:ℝ) → 0 < H →
      ∀ (j q h : ℕ) (Z Q : ℝ) (early : Bool), j ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower ρ X h) →
      ∀ (E₀ U P : Finset Eisenstein) (remaining : Eisenstein → Prop),
      (∀ e ∈ E₀, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      let S := stoppedIntervalSupport (Fin i) X (b/2) b 1
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 (distinguishedStoppingWeights d)
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j q h Z Q early)
      ‖∑ a ∈ P, ∑ b ∈ S, stoppedAlpha E₀ U primeDetectorCutoff (X^ξ) remaining a*β b*
        centeredHeightKernel 0 primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b)‖ ≤
        K*X^(5/6:ℝ)/(Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
