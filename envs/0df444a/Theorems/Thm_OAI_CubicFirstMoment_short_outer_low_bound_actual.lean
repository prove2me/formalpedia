-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_short_outer_low_bound_actual
-- name    : OAI.CubicFirstMoment.short_outer_low_bound_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:28:01.987051+00:00
-- url     : https://prove2.me/theorems/f366b4f3-d6c4-44d4-893b-ee131a1f0fc7
-- title:
--   OAI.CubicFirstMoment.short_outer_low_bound_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.short_outer_low_bound_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralShortOuterLow.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralShortOuterLow.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem short_outer_low_bound_actual
--       {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
--       (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
--       {A : ℝ} (hA : 0 ≤ A) (k Ct : ℕ) :
--       ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
--         (α : Eisenstein → ℂ) (X Y H X₀ : ℝ),
--         2 ≤ X → 1 ≤ Real.log X → Real.exp hW.radius ≤ X →
--         1 ≤ Y → 2*Y ≤ X^(51/100:ℝ) → 0 < H →
--         (∀ r ∈ S, primary r) →
--         (∀ r ∈ S, α r ≠ 0 → norm r ≤ Y) →
--         (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
--         ‖∑ r ∈ S, α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
--           if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
--             centeredHeightKernel ℓ (W (w r)) H ((1+Real.log X)^Ct) X X₀ (r*u) else 0‖ ≤
--           K*(1+Real.log Y)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` and `OAI.CubicFirstMoment.primaryElementBall` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.metaplecticPrimaryDivisors` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.centeredHeightKernel` and `OAI.CubicFirstMoment.squarefreeProductEnvelope` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.primeProductLowHeight_angular_isLittleO_actual` and `OAI.CubicFirstMoment.primeProductLowHeight_radial_isLittleO_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralShortOuterLow.lean (declaration OAI.CubicFirstMoment.short_outer_low_bound_actual)

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
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem short_outer_low_bound_actual
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {A : ℝ} (hA : 0 ≤ A) (k Ct : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X Y H X₀ : ℝ),
      2 ≤ X → 1 ≤ Real.log X → Real.exp hW.radius ≤ X →
      1 ≤ Y → 2*Y ≤ X^(51/100:ℝ) → 0 < H →
      (∀ r ∈ S, primary r) →
      (∀ r ∈ S, α r ≠ 0 → norm r ≤ Y) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*∑ u ∈ primaryElementBall (Real.exp hW.radius*X),
        if r*u ∈ squarefreeProductEnvelope (Real.exp hW.radius*X) then
          centeredHeightKernel ℓ (W (w r)) H ((1+Real.log X)^Ct) X X₀ (r*u) else 0‖ ≤
        K*(1+Real.log Y)*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
  sorry

end CubicFirstMoment

end

end OAI
end
