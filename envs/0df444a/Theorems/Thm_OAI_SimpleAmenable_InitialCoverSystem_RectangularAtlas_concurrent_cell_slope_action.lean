-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_RectangularAtlas_concurrent_cell_slope_action
-- name    : OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:39:10.27876+00:00
-- url     : https://prove2.me/theorems/c4c1bd3c-c5ca-4e19-9b27-e638d344d921
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ConcurrentCellSlopeAction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ConcurrentCellSlopeAction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem concurrent_cell_slope_action (hlarge : 20 ≤ m+1)
--       (hr : 0 < ordinary r ∧ ordinary r < 1/2) (ha : 0<a)
--       (q : Fin 2 → ℤ) (cell : Fin 2 → Fin C.mesh)
--       (d : Fin 2) (axis : Fin 4) (hne : slopeDirection d≠axis)
--       (z : CutRing × CutRing) (c : CutRing)
--       (hclip : ∀ k, -ordinary r ≤ ordinary (windowCut C.mesh (q k) (cell k).castSucc)-
--           ordinary (pointCoordinate z k) ∧
--         ordinary (windowCut C.mesh (q k) (cell k).succ)-ordinary (pointCoordinate z k) ≤ ordinary r)
--       (x y v w : GenericSquare a)
--       (hx : x ∈ (windowRectangle a C.mesh q cell).val)
--       (hy : y ∈ (windowRectangle a C.mesh q cell).val)
--       (hv : v ∈ (windowRectangle a C.mesh q cell).val)
--       (hw : w ∈ (windowRectangle a C.mesh q cell).val)
--       (hcx : cutForm a (slopeDirection d) (windowPlanarLift q x) ≤ ordinary (integralCutForm a (slopeDirection d) z))
--       (hcy : ordinary (integralCutForm a (slopeDirection d) z) ≤ cutForm a (slopeDirection d) (windowPlanarLift q y))
--       (hdv : cutForm a axis (windowPlanarLift q v) ≤ ordinary c)
--       (hdw : ordinary c ≤ cutForm a axis (windowPlanarLift q w)) :
--       ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
--         integralCutForm a (slopeDirection d) (u+C.anchors t (slopeDirection d))=
--           integralCutForm a (slopeDirection d) z ∧
--         integralCutForm a axis (u+C.anchors t axis)=c ∧
--         (∀ p : ℝ × ℝ,
--           (∀ k, ordinary (windowCut C.mesh (q k) (cell k).castSucc) ≤ realCoordinate p k ∧
--             realCoordinate p k ≤ ordinary (windowCut C.mesh (q k) (cell k).succ)) →
--           ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) < realCoordinate p k ∧
--             realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
--         (∀ b ∈ ({slopeDirection d,axis} : Set (Fin 4)), ∀ p : ℝ × ℝ,
--           (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p k ∧
--             realCoordinate p k ≤ ordinary ((C.margins t).upper k+pointCoordinate u k)) →
--           ∀ k, |realCoordinate p k-ordinary (pointCoordinate (u+C.anchors t b) k)|<3*C.epsilon) ∧
--         ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
--           B.AlignedSmallSupported f →
--           SmallControlled B.c f (B.windowSector (by omega) C.mesh (A.rectangles C.mesh) q
--             (windowRectangle a C.mesh q cell)) →
--           ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
--             ∀ b ∈ f.range,
--               A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s)*b*
--                   (A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
--                 A.slope (by omega) d (u+C.anchors t (slopeDirection d)) (universalMap (subtypeAlternatingHom I.val) s)*b*
--                   (A.slope (by omega) d (u+C.anchors t (slopeDirection d)) (universalMap (subtypeAlternatingHom I.val) s))⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.cutForm`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.integralCutForm`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup`, `OAI.SimpleAmenable.shortRelations` and `OAI.SimpleAmenable.universalMap` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ControlAlphabet`, `OAI.SimpleAmenable.VertexType`, `OAI.SimpleAmenable.controlAlphabet_perfect`, `OAI.SimpleAmenable.realCoordinate`, `OAI.SimpleAmenable.slopeDirection` and `OAI.SimpleAmenable.subtypeAlternatingHom` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.commonVertexDenominator`, `OAI.SimpleAmenable.pointCoordinate`, `OAI.SimpleAmenable.windowCut` and `OAI.SimpleAmenable.InitialCoverSystem.windowSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.vertexRepresentative` (definitions bundle `OAIQ65Sa006` of this split); `OAI.SimpleAmenable.windowPlanarLift` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.ConcurrentGeometry`, `OAI.SimpleAmenable.ConcurrentGeometryData` and `OAI.SimpleAmenable.VertexMargin` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas` (definitions bundle `OAIQ65Sa013` of this split); `OAI.SimpleAmenable.windowRectangle` (definitions bundle `OAIQ65Sa014` of this split); `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope` (definitions bundle `OAIQ65Sa015` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.crossing_cell_actions` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ConcurrentCellSlopeAction.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action)

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
section ConcurrentCellSlopeAction
namespace InitialCoverSystem.RectangularAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.RectangularAtlas) (C : ConcurrentGeometry a r)

theorem concurrent_cell_slope_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (ha : 0<a)
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin C.mesh)
    (d : Fin 2) (axis : Fin 4) (hne : slopeDirection d≠axis)
    (z : CutRing × CutRing) (c : CutRing)
    (hclip : ∀ k, -ordinary r ≤ ordinary (windowCut C.mesh (q k) (cell k).castSucc)-
        ordinary (pointCoordinate z k) ∧
      ordinary (windowCut C.mesh (q k) (cell k).succ)-ordinary (pointCoordinate z k) ≤ ordinary r)
    (x y v w : GenericSquare a)
    (hx : x ∈ (windowRectangle a C.mesh q cell).val)
    (hy : y ∈ (windowRectangle a C.mesh q cell).val)
    (hv : v ∈ (windowRectangle a C.mesh q cell).val)
    (hw : w ∈ (windowRectangle a C.mesh q cell).val)
    (hcx : cutForm a (slopeDirection d) (windowPlanarLift q x) ≤ ordinary (integralCutForm a (slopeDirection d) z))
    (hcy : ordinary (integralCutForm a (slopeDirection d) z) ≤ cutForm a (slopeDirection d) (windowPlanarLift q y))
    (hdv : cutForm a axis (windowPlanarLift q v) ≤ ordinary c)
    (hdw : ordinary c ≤ cutForm a axis (windowPlanarLift q w)) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      integralCutForm a (slopeDirection d) (u+C.anchors t (slopeDirection d))=
        integralCutForm a (slopeDirection d) z ∧
      integralCutForm a axis (u+C.anchors t axis)=c ∧
      (∀ p : ℝ × ℝ,
        (∀ k, ordinary (windowCut C.mesh (q k) (cell k).castSucc) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary (windowCut C.mesh (q k) (cell k).succ)) →
        ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) < realCoordinate p k ∧
          realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
      (∀ b ∈ ({slopeDirection d,axis} : Set (Fin 4)), ∀ p : ℝ × ℝ,
        (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary ((C.margins t).upper k+pointCoordinate u k)) →
        ∀ k, |realCoordinate p k-ordinary (pointCoordinate (u+C.anchors t b) k)|<3*C.epsilon) ∧
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
        B.AlignedSmallSupported f →
        SmallControlled B.c f (B.windowSector (by omega) C.mesh (A.rectangles C.mesh) q
          (windowRectangle a C.mesh q cell)) →
        ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
          ∀ b ∈ f.range,
            A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s)*b*
                (A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
              A.slope (by omega) d (u+C.anchors t (slopeDirection d)) (universalMap (subtypeAlternatingHom I.val) s)*b*
                (A.slope (by omega) d (u+C.anchors t (slopeDirection d)) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  sorry

end InitialCoverSystem.RectangularAtlas
end ConcurrentCellSlopeAction

end SimpleAmenable
end
end

end OAI
end
