-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_tailPrime_upper_group_bound_uniform
-- name    : OAI.CubicFirstMoment.tailPrime_upper_group_bound_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:47:12.66489+00:00
-- url     : https://prove2.me/theorems/a4695ad3-c65e-46a8-ae63-a150e0a935ea
-- title:
--   OAI.CubicFirstMoment.tailPrime_upper_group_bound_uniform: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.tailPrime_upper_group_bound_uniform` of [lean/OAI/NumberTheory/CubicMoment/Estimates/TailPrimeUpperGroupBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/TailPrimeUpperGroupBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem tailPrime_upper_group_bound_uniform
--       (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
--       (hperiod : CubicSupplementaryPeriodicity)
--       {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
--       ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/36 ∧
--         ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 2/5 →
--         ∀ (i j : ℕ) (s : Finset (Fin i ⊕ Fin j)) (k : ℕ),
--         ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
--         ∀ (z : largeTupleBoxIndex i j) (H T : ℝ), z.1.1 = X →
--         let B := largeTupleGroupLength s z
--         let A := largeTupleGroupLength (Finset.univ\s) z
--         X^(1/3-3*κ) ≤ B → B^2 ≤ 3*X →
--         X/(2*2^(i+j)) ≤ A*B → A*B ≤ 3*X →
--         (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
--         X^(1/100:ℝ) ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
--         ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
--           (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
--           (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
--           (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
--           primeProductEnvelope H T z.1.1‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.GammaQuotientStripBound` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound`, `OAI.CubicFirstMoment.largeTupleNormScale` and `OAI.CubicFirstMoment.primeProductEnvelope` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.largeTupleBoxIndex` and `OAI.CubicFirstMoment.largeTupleGroupLength` (definitions bundle `OAIQ096A006` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.envelopeCutoffBilinearTail`, `OAI.CubicFirstMoment.largeTupleOtherCoefficient` and `OAI.CubicFirstMoment.largeTupleSelectedCoefficient` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.largeTupleOtherSupport` and `OAI.CubicFirstMoment.largeTupleSelectedSupport` (definitions bundle `OAIQ096A019` of this split).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.tailHighUpperArity_isLittleO_uniform` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/TailPrimeUpperGroupBound.lean (declaration OAI.CubicFirstMoment.tailPrime_upper_group_bound_uniform)

import Mathlib
import Definitions.Def_OAIQ096A019

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailPrime_upper_group_bound_uniform
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/36 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 2/5 →
      ∀ (i j : ℕ) (s : Finset (Fin i ⊕ Fin j)) (k : ℕ),
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ), z.1.1 = X →
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      X^(1/3-3*κ) ≤ B → B^2 ≤ 3*X →
      X/(2*2^(i+j)) ≤ A*B → A*B ≤ 3*X →
      (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      X^(1/100:ℝ) ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ‖envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
        (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
        primeProductEnvelope H T z.1.1‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
