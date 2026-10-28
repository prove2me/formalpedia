-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_tangentChartTables_eventually
-- name    : OAI.SimpleAmenable.tangentChartTables_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:49:15.122491+00:00
-- url     : https://prove2.me/theorems/75c3cafb-6eb4-455d-8cdc-f60dfe2cbb5a
-- title:
--   OAI.SimpleAmenable.tangentChartTables_eventually: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.tangentChartTables_eventually` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/TangentChartTemplates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/TangentChartTemplates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem tangentChartTables_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
--       (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1)
--       (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) :
--       ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
--         ∀ d e z I b hb, B.PrimitiveFamilyLaw I b hb
--           (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.CutRing` and `OAI.SimpleAmenable.ordinary` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.InitialCoverSystem` and `OAI.SimpleAmenable.InitialCoverSystem.PrimitiveFamilyLaw` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.signedShortSteps`, `OAI.SimpleAmenable.tangentChartTemplate` and `OAI.SimpleAmenable.translatedTemplate` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.rectangularAtlas_fixed_radius_eventually` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/TangentChartTemplates.lean (declaration OAI.SimpleAmenable.tangentChartTables_eventually)

import Mathlib
import Definitions.Def_OAIQ65Sa011

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section TangentChartTemplates

theorem tangentChartTables_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      ∀ d e z I b hb, B.PrimitiveFamilyLaw I b hb
        (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z) := by
  sorry

end TangentChartTemplates

end SimpleAmenable
end
end

end OAI
end
