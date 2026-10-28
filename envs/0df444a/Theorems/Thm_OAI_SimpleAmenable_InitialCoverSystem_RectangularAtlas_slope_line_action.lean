-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_RectangularAtlas_slope_line_action
-- name    : OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:37:32.053491+00:00
-- url     : https://prove2.me/theorems/e60e3f26-7498-42c0-82cd-f1b3a8251283
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/RectangularAtlas.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/RectangularAtlas.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem slope_line_action (hlarge : 20 ≤ m+1)
--       (hr : 0 < ordinary r ∧ ordinary r < 1/2)
--       (d : Fin 2) (z z' : CutRing × CutRing)
--       (hline : integralCutForm a (slopeDirection d) z=integralCutForm a (slopeDirection d) z')
--       (L V : Fin 2 → CutRing) (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
--       (hz : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z j) ∧
--         ordinary (V j)-ordinary (pointCoordinate z j) ≤ ordinary r)
--       (hz' : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z' j) ∧
--         ordinary (V j)-ordinary (pointCoordinate z' j) ≤ ordinary r)
--       (x : ℝ × ℝ) (hx : cutForm a (slopeDirection d) x=ordinary (integralCutForm a (slopeDirection d) z))
--       (hnear : ∀ j, |ordinary (L j)-realCoordinate x j| ≤ ordinary r/4 ∧
--         |ordinary (V j)-realCoordinate x j| ≤ ordinary r/4)
--       (n : ℕ) (q : Fin 2 → ℤ)
--       (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
--         (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
--       (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
--       (hf : B.AlignedSmallSupported f)
--       (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles n) q (coordinateRectangle a L V)))
--       (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
--       (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
--       A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s)*t*
--         (A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
--       A.slope (by omega) d z' (universalMap (subtypeAlternatingHom I.val) s)*t*
--         (A.slope (by omega) d z' (universalMap (subtypeAlternatingHom I.val) s))⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.cutForm`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.integralCutForm`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup`, `OAI.SimpleAmenable.shortRelations` and `OAI.SimpleAmenable.universalMap` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ControlAlphabet`, `OAI.SimpleAmenable.ResolvedBy`, `OAI.SimpleAmenable.controlAlphabet_perfect`, `OAI.SimpleAmenable.realCoordinate`, `OAI.SimpleAmenable.slopeDirection` and `OAI.SimpleAmenable.subtypeAlternatingHom` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.coordinateWindowPrimitives`, `OAI.SimpleAmenable.pointCoordinate`, `OAI.SimpleAmenable.InitialCoverSystem.primitiveTests` and `OAI.SimpleAmenable.InitialCoverSystem.windowSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.coordinateRectangle` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas` (definitions bundle `OAIQ65Sa013` of this split); `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope` (definitions bundle `OAIQ65Sa015` of this split).
--
--   **Used by.** The proofs of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.selected_active_slope_actions`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action`, `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.inactive_near_action_neighborhood` and `OAI_SimpleAmenable_InitialCoverSystem_RectangularAtlas_inactive_quadrant_action` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/RectangularAtlas.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action)

import Mathlib
import Definitions.Def_OAIQ65Sa015

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section RectangularAtlas
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

namespace RectangularAtlas
variable {B} (A : B.RectangularAtlas)

theorem slope_line_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (d : Fin 2) (z z' : CutRing × CutRing)
    (hline : integralCutForm a (slopeDirection d) z=integralCutForm a (slopeDirection d) z')
    (L V : Fin 2 → CutRing) (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hz : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z j) ∧
      ordinary (V j)-ordinary (pointCoordinate z j) ≤ ordinary r)
    (hz' : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z' j) ∧
      ordinary (V j)-ordinary (pointCoordinate z' j) ≤ ordinary r)
    (x : ℝ × ℝ) (hx : cutForm a (slopeDirection d) x=ordinary (integralCutForm a (slopeDirection d) z))
    (hnear : ∀ j, |ordinary (L j)-realCoordinate x j| ≤ ordinary r/4 ∧
      |ordinary (V j)-realCoordinate x j| ≤ ordinary r/4)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles n) q (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
    A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s)*t*
      (A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    A.slope (by omega) d z' (universalMap (subtypeAlternatingHom I.val) s)*t*
      (A.slope (by omega) d z' (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  sorry

end RectangularAtlas
end InitialCoverSystem

end RectangularAtlas

end SimpleAmenable
end
end

end OAI
end
