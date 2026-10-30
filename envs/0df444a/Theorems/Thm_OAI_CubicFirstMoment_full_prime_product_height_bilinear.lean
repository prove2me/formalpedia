-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_full_prime_product_height_bilinear
-- name    : OAI.CubicFirstMoment.full_prime_product_height_bilinear
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:26:05.192251+00:00
-- url     : https://prove2.me/theorems/8c9e1f50-891c-4c4d-989d-5ee1f0a8a243
-- title:
--   OAI.CubicFirstMoment.full_prime_product_height_bilinear: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.full_prime_product_height_bilinear` of [lean/OAI/NumberTheory/CubicMoment/Estimates/GroupedPrimeHeight.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/GroupedPrimeHeight.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem full_prime_product_height_bilinear
--       (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
--       (hperiod : CubicSupplementaryPeriodicity)
--       {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
--       (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
--       (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
--       (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
--       (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
--       (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
--       (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
--       (hAhi : ∀ r i x, R < x → WA r i x = 0)
--       (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
--       (hBhi : ∀ r i x, R < x → WB r i x = 0) (k : ℕ) :
--       ∃ (η σ : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
--         ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (eA eB : Eisenstein) (u T : ℝ),
--         B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
--         (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
--         (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
--         eB ≠ 0 → norm eB ≤ (LB r)^σ →
--         (1+Real.log (LB r))^m ≤ T → T ≤ (LB r)^(7/20:ℝ) → |u| ≤ (LB r)^(7/20:ℝ) →
--         dyadicHeightMean (fun t =>
--           ‖∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
--             ∑ y ∈ fullSquarefreePrimeSupport R (WB r) XB eB,
--               fullPrimeCoefficient R (WA r) XA x*fullPrimeCoefficient R (WB r) XB y*
--                 gauss (x*y)*normTwist (u+t) (x*y)‖) T ≤
--           K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.normTwist` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder`, `OAI.CubicFirstMoment.GammaQuotientStripBound` and `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.MontgomeryVaughanBound` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.dyadicHeightMean` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.gauss` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` and `OAI.CubicFirstMoment.fullPrimeCoefficient` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.fullSquarefreePrimeSupport` (definitions bundle `OAIQ096A011` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.centralRoughProduct_sub_low_scale_isLittleO_actual`, `OAI.CubicFirstMoment.largePrimeTupleHighSum_isLittleO_actual`, `OAI.CubicFirstMoment.largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI_CubicFirstMoment_large_tuple_restricted_smoothed_actual`, `OAI_CubicFirstMoment_semiprimeGaussTail_hecke_window`, `OAI.CubicFirstMoment.semiprimeGaussTail_piece_log_saving`, `OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO`, `OAI_CubicFirstMoment_tailPrime_hecke_group`, `OAI_CubicFirstMoment_tailPrime_hecke_window` and `OAI.CubicFirstMoment.tailPrime_upper_group_bound_uniform` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/GroupedPrimeHeight.lean (declaration OAI.CubicFirstMoment.full_prime_product_height_bilinear)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem full_prime_product_height_bilinear
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0) (k : ℕ) :
    ∃ (η σ : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (eA eB : Eisenstein) (u T : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      eB ≠ 0 → norm eB ≤ (LB r)^σ →
      (1+Real.log (LB r))^m ≤ T → T ≤ (LB r)^(7/20:ℝ) → |u| ≤ (LB r)^(7/20:ℝ) →
      dyadicHeightMean (fun t =>
        ‖∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
          ∑ y ∈ fullSquarefreePrimeSupport R (WB r) XB eB,
            fullPrimeCoefficient R (WA r) XA x*fullPrimeCoefficient R (WB r) XB y*
              gauss (x*y)*normTwist (u+t) (x*y)‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
