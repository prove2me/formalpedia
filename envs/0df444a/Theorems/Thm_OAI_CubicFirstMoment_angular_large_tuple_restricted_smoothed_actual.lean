-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_large_tuple_restricted_smoothed_actual
-- name    : OAI.CubicFirstMoment.angular_large_tuple_restricted_smoothed_actual
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:34:16.117203+00:00
-- url     : https://prove2.me/theorems/345a0c57-43cd-4e61-b9b3-224f98f89f96
-- title:
--   OAI.CubicFirstMoment.angular_large_tuple_restricted_smoothed_actual: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_large_tuple_restricted_smoothed_actual` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularLargeTupleRestrictedSmoothed.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularLargeTupleRestrictedSmoothed.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_large_tuple_restricted_smoothed_actual {i j : ℕ}
--       (s : Finset (Fin i ⊕ Fin j)) (hs : s.Nonempty)
--       (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
--       (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
--         AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k U : ℕ) :
--       ∃ (η : ℝ) (G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
--         ∀ (z : largeTupleBoxIndex i j) (u : ℝ),
--         let B := largeTupleGroupLength s z
--         let A := largeTupleGroupLength (Finset.univ\s) z
--         T₀ ≤ B → (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
--         B^(1-η/16) ≤ A → A ≤ B^2/(1+Real.log B)^G → |u| ≤ (1+Real.log B)^U →
--         ‖largeTupleSmoothedPolynomial ℓ ξ z.1.1 z.1.2 s u‖ ≤
--           K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` and `OAI.CubicFirstMoment.largeTupleNormScale` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.metaplecticAngularShift` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.AngularKummerPrimeExplicitEstimate` and `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.largeTupleBoxIndex` and `OAI.CubicFirstMoment.largeTupleGroupLength` (definitions bundle `OAIQ096A006` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.largeTupleSmoothedPolynomial` (definitions bundle `OAIQ096A019` of this split).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_largePrimeTupleHighSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI.CubicFirstMoment.angular_primeProductLowHeight_sub_low_scale_isLittleO_actual` and `OAI_CubicFirstMoment_angular_scaleFirstMiddleSum_isLittleO_actual` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaCentralAngularLargeTupleRestrictedSmoothed.lean (declaration OAI.CubicFirstMoment.angular_large_tuple_restricted_smoothed_actual)

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
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_large_tuple_restricted_smoothed_actual {i j : ℕ}
    (s : Finset (Fin i ⊕ Fin j)) (hs : s.Nonempty)
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k U : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (z : largeTupleBoxIndex i j) (u : ℝ),
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      T₀ ≤ B → (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      B^(1-η/16) ≤ A → A ≤ B^2/(1+Real.log B)^G → |u| ≤ (1+Real.log B)^U →
      ‖largeTupleSmoothedPolynomial ℓ ξ z.1.1 z.1.2 s u‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
