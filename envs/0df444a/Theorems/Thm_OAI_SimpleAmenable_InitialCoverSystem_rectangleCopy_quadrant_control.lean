-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_rectangleCopy_quadrant_control
-- name    : OAI.SimpleAmenable.InitialCoverSystem.rectangleCopy_quadrant_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:17:17.657581+00:00
-- url     : https://prove2.me/theorems/8b10cccc-4320-409e-901f-c5ec7c6085d0
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.rectangleCopy_quadrant_control: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.rectangleCopy_quadrant_control` of [lean/OAI/GroupTheory/SimpleAmenable/Configurations/Rectangles.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/Rectangles.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem rectangleCopy_quadrant_control (hlarge : 20 ≤ m+1)
--       (hr : 0 < ordinary r ∧ ordinary r < 1/2)
--       (s u : CutRing) (hs : 0 < ordinary s ∧ ordinary s < ordinary r)
--       (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u)
--       {n : ℕ} (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n)
--       (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) (fit : R.ChartFit s z)
--       (hlo : ∀ j, ordinary (signQuadrantLower s d positive j)+ordinary (pointCoordinate z j) ≤ ordinary (R.lower j))
--       (hup : ∀ j, ordinary (R.upper j) ≤ ordinary (signQuadrantUpper s d positive j)+ordinary (pointCoordinate z j)) :
--       SmallControlled B.c (B.rectangleCopy (by omega) g R)
--         (B.tangentSign (by omega) (symmetricWindowLength s) (symmetricWindowStart s) u h d z positive)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.LabelledRectangle`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.pointCoordinate` and `OAI.SimpleAmenable.InitialCoverSystem.CoordinateWindowLaw` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.symmetricWindowStart` (definitions bundle `OAIQ65Sa008` of this split); `OAI.SimpleAmenable.signQuadrantLower` and `OAI.SimpleAmenable.signQuadrantUpper` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.symmetricWindowLength` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.TangentChartLaws` and `OAI.SimpleAmenable.InitialCoverSystem.tangentSign` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.InitialCoverSystem.rectangleCopy` and `OAI.SimpleAmenable.LabelledRectangle.ChartFit` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.separated_old_rectangles_commute` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/Rectangles.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.rectangleCopy_quadrant_control)

import Mathlib
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section OldRectangles

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem rectangleCopy_quadrant_control (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u : CutRing) (hs : 0 < ordinary s ∧ ordinary s < ordinary r)
    (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u)
    {n : ℕ} (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) (fit : R.ChartFit s z)
    (hlo : ∀ j, ordinary (signQuadrantLower s d positive j)+ordinary (pointCoordinate z j) ≤ ordinary (R.lower j))
    (hup : ∀ j, ordinary (R.upper j) ≤ ordinary (signQuadrantUpper s d positive j)+ordinary (pointCoordinate z j)) :
    SmallControlled B.c (B.rectangleCopy (by omega) g R)
      (B.tangentSign (by omega) (symmetricWindowLength s) (symmetricWindowStart s) u h d z positive) := by
  sorry

end InitialCoverSystem
end OldRectangles

end SimpleAmenable
end
end

end OAI
end
