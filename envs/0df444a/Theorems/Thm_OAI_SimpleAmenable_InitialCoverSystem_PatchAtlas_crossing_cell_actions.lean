-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_crossing_cell_actions
-- name    : OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.crossing_cell_actions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:34:52.079299+00:00
-- url     : https://prove2.me/theorems/a5c01f3e-a921-489a-ac6c-d9776819c0a3
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.crossing_cell_actions: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.crossing_cell_actions` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CrossingCellActions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CrossingCellActions.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem crossing_cell_actions {ι κ : Type*} [Finite ι] [Finite κ]
--       (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
--       (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
--       (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
--       (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
--       (i : ι) (i' : κ) (d j : Fin 2) (v : CutRing × CutRing)
--       (hP : P i=(slopeTestIndex d,0)) (hQ : Q i'=(coordinateTestIndex j,v))
--       (q : Fin 2 → ℤ) (cell : Fin 2 → Fin A.geometry.mesh)
--       (k : Fin 2 → ℤ) (c : CutRing) (positive : Bool)
--       (hk : ∀ l, -ordinary r ≤ ordinary (windowCut A.geometry.mesh (q l) (cell l).castSucc)+(k l:ℝ) ∧
--         ordinary (windowCut A.geometry.mesh (q l) (cell l).succ)+(k l:ℝ) ≤ ordinary r)
--       (hc : ∀ p ∈ (windowRectangle a A.geometry.mesh q cell).val,
--         (p ∈ (spatialTranslate v (coordinatePrimitive a j)).val ↔
--           if positive then ordinary c ≤ realCoordinate (windowPlanarLift q p) j
--           else realCoordinate (windowPlanarLift q p) j<ordinary c))
--       (x y v' w : GenericSquare a)
--       (hx : x ∈ (windowRectangle a A.geometry.mesh q cell).val)
--       (hy : y ∈ (windowRectangle a A.geometry.mesh q cell).val)
--       (hv : v' ∈ (windowRectangle a A.geometry.mesh q cell).val)
--       (hw : w ∈ (windowRectangle a A.geometry.mesh q cell).val)
--       (hcx : cutForm a (slopeDirection d) (windowPlanarLift q x) ≤
--         ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing))))
--       (hcy : ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing))) ≤
--         cutForm a (slopeDirection d) (windowPlanarLift q y))
--       (hdv : cutForm a (axisDirection j) (windowPlanarLift q v') ≤ ordinary c)
--       (hdw : ordinary c ≤ cutForm a (axisDirection j) (windowPlanarLift q w)) :
--       ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
--         windowRectangle a A.geometry.mesh q cell ≤ A.margin t u ∧
--         ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
--           B.AlignedSmallSupported f →
--           SmallControlled B.c f (B.windowSector (by omega) A.geometry.mesh
--             (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell)) →
--           ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
--             ∀ b ∈ f.range,
--               (B.fullGeometricSector (by omega) P h (clippedSlopePrimitive a r (slopeDirection d))
--                   (universalMap (subtypeAlternatingHom I.val) s)*b*
--                 (B.fullGeometricSector (by omega) P h (clippedSlopePrimitive a r (slopeDirection d))
--                   (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
--               B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
--                   (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
--                     (clippedSlopePrimitive a r (slopeDirection d)))
--                   (universalMap (subtypeAlternatingHom I.val) s)*b*
--                 (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
--                   (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
--                     (clippedSlopePrimitive a r (slopeDirection d)))
--                   (universalMap (subtypeAlternatingHom I.val) s))⁻¹) ∧
--               (B.fullGeometricSector (by omega) Q g (spatialTranslate v (coordinatePrimitive a j))
--                   (universalMap (subtypeAlternatingHom I.val) s)*b*
--                 (B.fullGeometricSector (by omega) Q g (spatialTranslate v (coordinatePrimitive a j))
--                   (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
--               B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
--                   (if positive then spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j)
--                     else (spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ)
--                   (universalMap (subtypeAlternatingHom I.val) s)*b*
--                 (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
--                   (if positive then spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j)
--                     else (spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ)
--                   (universalMap (subtypeAlternatingHom I.val) s))⁻¹)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.clippedSlopePrimitive`, `OAI.SimpleAmenable.coordinatePrimitive`, `OAI.SimpleAmenable.cutForm`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.integralCutForm`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup`, `OAI.SimpleAmenable.shortRelations` and `OAI.SimpleAmenable.universalMap` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ControlAlphabet`, `OAI.SimpleAmenable.VertexType`, `OAI.SimpleAmenable.axisDirection`, `OAI.SimpleAmenable.controlAlphabet_perfect`, `OAI.SimpleAmenable.coordinateTestIndex`, `OAI.SimpleAmenable.realCoordinate`, `OAI.SimpleAmenable.slopeDirection`, `OAI.SimpleAmenable.slopeTestIndex` and `OAI.SimpleAmenable.subtypeAlternatingHom` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.commonVertexDenominator`, `OAI.SimpleAmenable.spatialTranslate`, `OAI.SimpleAmenable.windowCut`, `OAI.SimpleAmenable.InitialCoverSystem.PrimitiveFamilyLaw`, `OAI.SimpleAmenable.InitialCoverSystem.fullGeometricSector` and `OAI.SimpleAmenable.InitialCoverSystem.windowSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.windowPlanarLift` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.ConcurrentGeometryData` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas` and `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas` (definitions bundle `OAIQ65Sa013` of this split); `OAI.SimpleAmenable.windowRectangle` (definitions bundle `OAIQ65Sa014` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.concurrentLaw`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.concurrentPrimitives` and `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.margin` (definitions bundle `OAIQ65Sa015` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CrossingCellActions.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.crossing_cell_actions)

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
section CrossingCellActions

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2  ≤  m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas)

theorem crossing_cell_actions {ι κ : Type*} [Finite ι] [Finite κ]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (i : ι) (i' : κ) (d j : Fin 2) (v : CutRing × CutRing)
    (hP : P i=(slopeTestIndex d,0)) (hQ : Q i'=(coordinateTestIndex j,v))
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin A.geometry.mesh)
    (k : Fin 2 → ℤ) (c : CutRing) (positive : Bool)
    (hk : ∀ l, -ordinary r ≤ ordinary (windowCut A.geometry.mesh (q l) (cell l).castSucc)+(k l:ℝ) ∧
      ordinary (windowCut A.geometry.mesh (q l) (cell l).succ)+(k l:ℝ) ≤ ordinary r)
    (hc : ∀ p ∈ (windowRectangle a A.geometry.mesh q cell).val,
      (p ∈ (spatialTranslate v (coordinatePrimitive a j)).val ↔
        if positive then ordinary c ≤ realCoordinate (windowPlanarLift q p) j
        else realCoordinate (windowPlanarLift q p) j<ordinary c))
    (x y v' w : GenericSquare a)
    (hx : x ∈ (windowRectangle a A.geometry.mesh q cell).val)
    (hy : y ∈ (windowRectangle a A.geometry.mesh q cell).val)
    (hv : v' ∈ (windowRectangle a A.geometry.mesh q cell).val)
    (hw : w ∈ (windowRectangle a A.geometry.mesh q cell).val)
    (hcx : cutForm a (slopeDirection d) (windowPlanarLift q x) ≤
      ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing))))
    (hcy : ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing))) ≤
      cutForm a (slopeDirection d) (windowPlanarLift q y))
    (hdv : cutForm a (axisDirection j) (windowPlanarLift q v') ≤ ordinary c)
    (hdw : ordinary c ≤ cutForm a (axisDirection j) (windowPlanarLift q w)) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      windowRectangle a A.geometry.mesh q cell ≤ A.margin t u ∧
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
        B.AlignedSmallSupported f →
        SmallControlled B.c f (B.windowSector (by omega) A.geometry.mesh
          (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell)) →
        ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
          ∀ b ∈ f.range,
            (B.fullGeometricSector (by omega) P h (clippedSlopePrimitive a r (slopeDirection d))
                (universalMap (subtypeAlternatingHom I.val) s)*b*
              (B.fullGeometricSector (by omega) P h (clippedSlopePrimitive a r (slopeDirection d))
                (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
            B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
                (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
                  (clippedSlopePrimitive a r (slopeDirection d)))
                (universalMap (subtypeAlternatingHom I.val) s)*b*
              (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
                (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
                  (clippedSlopePrimitive a r (slopeDirection d)))
                (universalMap (subtypeAlternatingHom I.val) s))⁻¹) ∧
            (B.fullGeometricSector (by omega) Q g (spatialTranslate v (coordinatePrimitive a j))
                (universalMap (subtypeAlternatingHom I.val) s)*b*
              (B.fullGeometricSector (by omega) Q g (spatialTranslate v (coordinatePrimitive a j))
                (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
            B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
                (if positive then spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j)
                  else (spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ)
                (universalMap (subtypeAlternatingHom I.val) s)*b*
              (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
                (if positive then spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j)
                  else (spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ)
                (universalMap (subtypeAlternatingHom I.val) s))⁻¹) := by
  sorry

end InitialCoverSystem.PatchAtlas
end CrossingCellActions

section LocalPatchTemplates
namespace InitialCoverSystem

attribute [instance] LocalPatchTemplate.finite_index

end InitialCoverSystem
end LocalPatchTemplates

end SimpleAmenable
end
end

end OAI
end
