-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_flagSignal_good_row_constants
-- name    : OAI.SimpleAmenable.flagSignal_good_row_constants
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:23:55.913985+00:00
-- url     : https://prove2.me/theorems/b6955e5e-ac99-4c3c-84e3-a2c2d7f2efad
-- title:
--   OAI.SimpleAmenable.flagSignal_good_row_constants: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.flagSignal_good_row_constants` of [lean/OAI/GroupTheory/SimpleAmenable/RandomFields/SignalGoodRows.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/SignalGoodRows.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical`):
--
--   ```lean
--   theorem flagSignal_good_row_constants {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
--       (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
--       (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K : ℝ)
--       (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
--       (hχ : ∀x,‖x‖ ≤ K+2 → χ x=1) :
--       ∃R Q Cv Ca : ℝ,0 ≤ R ∧ 0 ≤ Q ∧ 0 ≤ Cv ∧ 0 ≤ Ca ∧
--         (∀N : ℝ,0<N → ∀z : FlagSite a m D v,
--           |flagSignalDifference hD g (fun x => q+ψ x) N z| ≤ Ca/N) ∧
--         ∀(N r η κ : ℝ),0<N → Q ≤ N → 0 < r → 0<η → η ≤ 1 → 0<κ →
--           36 ≤ r*η → 1 ≤ 2*κ/(r/N) → R ≤ κ/(r/N) →
--           ∀(z : FlagSite a m D v) (J : Finset (FlagSite a m D v)),flagGoodRow (r/N) κ z →
--           (∀w,w∉J → flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*
--             flagSignalDifference hD g (fun x => q+ψ x) N w=0) →
--           |(∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*
--             flagSignalDifference hD g (fun x => q+ψ x) N w)-
--             flagSignalDifference hD g (fun x => q+ψ x) N z| ≤
--             (Cv*η/N)*(1+38880/((D:ℝ)*Real.sqrt (r*η)))+
--             (Ca/N)*(38880/((D:ℝ)*Real.sqrt (r*η)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.FlagSite` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.flagGoodRow` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.flagAveragingMatrix` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.flagSignalDifference` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.polygon_signal_approx_identity` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/RandomFields/SignalGoodRows.lean (declaration OAI.SimpleAmenable.flagSignal_good_row_constants)

import Mathlib
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section SignalGoodRows
open Classical

theorem flagSignal_good_row_constants {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K : ℝ)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,‖x‖ ≤ K+2 → χ x=1) :
    ∃R Q Cv Ca : ℝ,0 ≤ R ∧ 0 ≤ Q ∧ 0 ≤ Cv ∧ 0 ≤ Ca ∧
      (∀N : ℝ,0<N → ∀z : FlagSite a m D v,
        |flagSignalDifference hD g (fun x => q+ψ x) N z| ≤ Ca/N) ∧
      ∀(N r η κ : ℝ),0<N → Q ≤ N → 0 < r → 0<η → η ≤ 1 → 0<κ →
        36 ≤ r*η → 1 ≤ 2*κ/(r/N) → R ≤ κ/(r/N) →
        ∀(z : FlagSite a m D v) (J : Finset (FlagSite a m D v)),flagGoodRow (r/N) κ z →
        (∀w,w∉J → flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*
          flagSignalDifference hD g (fun x => q+ψ x) N w=0) →
        |(∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*
          flagSignalDifference hD g (fun x => q+ψ x) N w)-
          flagSignalDifference hD g (fun x => q+ψ x) N z| ≤
          (Cv*η/N)*(1+38880/((D:ℝ)*Real.sqrt (r*η)))+
          (Ca/N)*(38880/((D:ℝ)*Real.sqrt (r*η))) := by
  sorry

end SignalGoodRows

end SimpleAmenable
end
end

end OAI
end
