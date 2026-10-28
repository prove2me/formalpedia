-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_interior_clipped_model_action_neighborhood
-- name    : OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.interior_clipped_model_action_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:35:31.489789+00:00
-- url     : https://prove2.me/theorems/f397e038-2e37-4a20-9df4-efbd80bdabc6
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.interior_clipped_model_action_neighborhood: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.interior_clipped_model_action_neighborhood` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FarClippedModels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FarClippedModels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas`, with `open scoped symmDiff`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem interior_clipped_model_action_neighborhood {ι : Type*} [Finite ι]
--       (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
--       (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ)
--       (G : ClippedGerm a r (slopeDirection d) u z)
--       {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
--       (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
--       (lo hi : Fin 2 → ι) (slope : ι)
--       (hlo : ∀ k, j (lo k)=axisDirection k ∧ c (lo k)=pointCoordinate G.offset k-r)
--       (hhi : ∀ k, j (hi k)=axisDirection k ∧ c (hi k)=pointCoordinate G.offset k+r)
--       (hs : j slope=slopeDirection d ∧ c slope=integralCutForm a (slopeDirection d) G.offset)
--       (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
--         (spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))).val)
--       (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
--       (σ : Fin 2 × Bool → Bool) (hσ : ∀ k, σ (k,false)=false ∧ σ (k,true)=true)
--       : ∃ δ : ℝ, 0<δ ∧ ∀ L V : Fin 2 → CutRing,
--       (∀ k, ordinary (L k) ≤ ordinary (V k)) →
--       (∀ k, -ordinary r≤ordinary (L k)-ordinary (pointCoordinate G.offset k) ∧
--         ordinary (V k)-ordinary (pointCoordinate G.offset k)≤ordinary r) →
--       (∀ k, |ordinary (L k)-realCoordinate z k|<δ ∧
--         |ordinary (V k)-realCoordinate z k|<δ) →
--       ∀ (n : ℕ) (q : Fin 2 → ℤ),
--       (ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
--         (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val) →
--       (coordinateRectangle a L V ≤
--         A.geometry.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ) →
--       ∀ (cell : Fin 2 → Fin A.geometry.mesh),
--       (coordinateRectangle a L V ≤ spatialTranslate G.offset
--         (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)) →
--       ∀ p : GenericSquare a, p ∈ (coordinateRectangle a L V).val → dist p.val z<δ →
--       (∀ k, ordinary (L k) ≤ realCoordinate p.val k ∧ realCoordinate p.val k<ordinary (V k)) →
--       ∀ (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
--       B.AlignedSmallSupported f →
--       (SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
--         (coordinateRectangle a L V))) →
--       ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
--       ∀ x ∈ f.range,
--       A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
--         (A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
--       B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
--         (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
--           (universalMap (subtypeAlternatingHom I.val) s)*x*
--         (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
--           (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
--             (universalMap (subtypeAlternatingHom I.val) s))⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.AvoidsCuts`, `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.clippedSlopePrimitive`, `OAI.SimpleAmenable.cutTau`, `OAI.SimpleAmenable.halfPlane`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.integralCutForm`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup`, `OAI.SimpleAmenable.shortRelations` and `OAI.SimpleAmenable.universalMap` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ControlAlphabet`, `OAI.SimpleAmenable.ResolvedBy`, `OAI.SimpleAmenable.axisDirection`, `OAI.SimpleAmenable.controlAlphabet_perfect`, `OAI.SimpleAmenable.realCoordinate`, `OAI.SimpleAmenable.slopeDirection`, `OAI.SimpleAmenable.slopeTestIndex` and `OAI.SimpleAmenable.subtypeAlternatingHom` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.commonVertexDenominator`, `OAI.SimpleAmenable.coordinateWindowPrimitives`, `OAI.SimpleAmenable.pointCoordinate`, `OAI.SimpleAmenable.spatialTranslate`, `OAI.SimpleAmenable.InitialCoverSystem.fullGeometricSector`, `OAI.SimpleAmenable.InitialCoverSystem.primitiveTests` and `OAI.SimpleAmenable.InitialCoverSystem.windowSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.symmetricWindowStart` (definitions bundle `OAIQ65Sa008` of this split); `OAI.SimpleAmenable.ClippedGerm`, `OAI.SimpleAmenable.coordinateRectangle`, `OAI.SimpleAmenable.ClippedGerm.axialCut`, `OAI.SimpleAmenable.ClippedGerm.offset`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart`, `OAI.SimpleAmenable.ConcurrentGeometry.coordinateGate`, `OAI.SimpleAmenable.ConcurrentGeometryData`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.offset`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.polygons` and `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.vertex` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas` and `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas` (definitions bundle `OAIQ65Sa013` of this split); `OAI.SimpleAmenable.windowRectangle` (definitions bundle `OAIQ65Sa014` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.concurrentLaw`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.concurrentPrimitives` and `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitiveStar` (definitions bundle `OAIQ65Sa015` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.uniform_clipped_model_action_neighborhood` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FarClippedModels.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.interior_clipped_model_action_neighborhood)

import Mathlib
import Definitions.Def_OAIQ65Sa015

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem interior_clipped_model_action_neighborhood {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (G : ClippedGerm a r (slopeDirection d) u z)
    {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (slope : ι)
    (hlo : ∀ k, j (lo k)=axisDirection k ∧ c (lo k)=pointCoordinate G.offset k-r)
    (hhi : ∀ k, j (hi k)=axisDirection k ∧ c (hi k)=pointCoordinate G.offset k+r)
    (hs : j slope=slopeDirection d ∧ c slope=integralCutForm a (slopeDirection d) G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))).val)
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
    (σ : Fin 2 × Bool → Bool) (hσ : ∀ k, σ (k,false)=false ∧ σ (k,true)=true)
    : ∃ δ : ℝ, 0<δ ∧ ∀ L V : Fin 2 → CutRing,
    (∀ k, ordinary (L k) ≤ ordinary (V k)) →
    (∀ k, -ordinary r≤ordinary (L k)-ordinary (pointCoordinate G.offset k) ∧
      ordinary (V k)-ordinary (pointCoordinate G.offset k)≤ordinary r) →
    (∀ k, |ordinary (L k)-realCoordinate z k|<δ ∧
      |ordinary (V k)-realCoordinate z k|<δ) →
    ∀ (n : ℕ) (q : Fin 2 → ℤ),
    (ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val) →
    (coordinateRectangle a L V ≤
      A.geometry.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ) →
    ∀ (cell : Fin 2 → Fin A.geometry.mesh),
    (coordinateRectangle a L V ≤ spatialTranslate G.offset
      (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)) →
    ∀ p : GenericSquare a, p ∈ (coordinateRectangle a L V).val → dist p.val z<δ →
    (∀ k, ordinary (L k) ≤ realCoordinate p.val k ∧ realCoordinate p.val k<ordinary (V k)) →
    ∀ (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
    B.AlignedSmallSupported f →
    (SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (coordinateRectangle a L V))) →
    ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
    ∀ x ∈ f.range,
    A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
      (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  sorry

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
end
