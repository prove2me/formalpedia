-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_flagAveragingMatrix_good_row_error
-- name    : OAI.SimpleAmenable.flagAveragingMatrix_good_row_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:19:09.456186+00:00
-- url     : https://prove2.me/theorems/53219140-cae8-419a-bb02-f6987386f6df
-- title:
--   OAI.SimpleAmenable.flagAveragingMatrix_good_row_error: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.flagAveragingMatrix_good_row_error` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/WeightedAveragingError.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/WeightedAveragingError.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical`):
--
--   ```lean
--   theorem flagAveragingMatrix_good_row_error {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
--       (χ : (ℝ×ℝ) → ℝ) (h : FlagSite a m D v → ℝ) {N r η κ E H : ℝ}
--       (hN : 0<N) (hr : 0 < r) (hη : 0<η) (hκ : 0<κ)
--       (hscale : 36 ≤ r*η) (hline : 1 ≤ 2*κ/(r/N))
--       (hE : 0 ≤ E) (z : FlagSite a m D v) (hz : flagGoodRow (r/N) κ z)
--       (hH : |h z| ≤ H)
--       (hχ : ∀w,flagRowTent (r/N) (N*η) z w≠0 → h w≠0 →
--         χ (scaledSiteConjugate N z)=1 ∧ χ (scaledSiteConjugate N w)=1)
--       (hnear : ∀w,flagRowTent (r/N) (N*η) z w≠0 → |h w-h z| ≤ E) :
--       ∃T : Finset (FlagSite a m D v),
--         (∀w,w∉T → flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w=0) ∧
--         |(∑w∈T,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z| ≤
--           E*(1+38880/((D:ℝ)*Real.sqrt (r*η)))+H*(38880/((D:ℝ)*Real.sqrt (r*η)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.FlagSite` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.flagGoodRow` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.flagAveragingMatrix` and `OAI.SimpleAmenable.scaledSiteConjugate` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.flagRowTent` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.flagSignal_good_row_constants` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/WeightedAveragingError.lean (declaration OAI.SimpleAmenable.flagAveragingMatrix_good_row_error)

import Mathlib
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section GoodRowAveraging
open Classical

theorem flagAveragingMatrix_good_row_error {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (h : FlagSite a m D v → ℝ) {N r η κ E H : ℝ}
    (hN : 0<N) (hr : 0 < r) (hη : 0<η) (hκ : 0<κ)
    (hscale : 36 ≤ r*η) (hline : 1 ≤ 2*κ/(r/N))
    (hE : 0 ≤ E) (z : FlagSite a m D v) (hz : flagGoodRow (r/N) κ z)
    (hH : |h z| ≤ H)
    (hχ : ∀w,flagRowTent (r/N) (N*η) z w≠0 → h w≠0 →
      χ (scaledSiteConjugate N z)=1 ∧ χ (scaledSiteConjugate N w)=1)
    (hnear : ∀w,flagRowTent (r/N) (N*η) z w≠0 → |h w-h z| ≤ E) :
    ∃T : Finset (FlagSite a m D v),
      (∀w,w∉T → flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w=0) ∧
      |(∑w∈T,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z| ≤
        E*(1+38880/((D:ℝ)*Real.sqrt (r*η)))+H*(38880/((D:ℝ)*Real.sqrt (r*η))) := by
  sorry

end GoodRowAveraging

end SimpleAmenable
end
end

end OAI
end
