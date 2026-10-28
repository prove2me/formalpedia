-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_slope_coordinate_cell_template
-- name    : OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:22:26.258921+00:00
-- url     : https://prove2.me/theorems/84009577-2944-42ac-adb8-696eeae76e19
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ConstantCellTemplates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ConstantCellTemplates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem slope_coordinate_cell_template {κ : Type} [Finite κ] {J : Type*}
--       (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
--       (d j : Fin 2) (v : CutRing × CutRing)
--       (P : Fin 2 → κ → Fin 5 × (CutRing × CutRing))
--       (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P i))
--       (i₀ i₁ : κ) (hP : P 0 i₀=(slopeTestIndex d,0)) (hQ : P 1 i₁=(coordinateTestIndex j,v))
--       (F : Option (Fin 2) → TrackStar (Fin (m+1)) →*
--         BoundedRelationCover M (alternatingGenerator a r m hm))
--       (f : J → TrackStar (Fin (m+1)) →*
--         BoundedRelationCover M (alternatingGenerator a r m hm))
--       (hF : ∀ i, F (some i)=B.fullGeometricSector (by omega) (P i) (h i)
--         (![clippedSlopePrimitive a r (slopeDirection d),spatialTranslate v (coordinatePrimitive a j)] i))
--       (q : Fin 2 → ℤ) (cell : Fin 2 → Fin A.geometry.mesh)
--       (hb : ∀ k, q k ≤ endpointLabel (-r) ∧ endpointLabel (-r)<q k+A.geometry.mesh)
--       (he : ∀ k, q k ≤ endpointLabel r ∧ endpointLabel r<q k+A.geometry.mesh)
--       (hW : ∀ i, ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r) (P i) s).val)
--         (windowRectangle a A.geometry.mesh q cell).val)
--       (hcoherent : ∀ i, B.fullGeometricSector (by omega) (P i) (h i)
--         (windowRectangle a A.geometry.mesh q cell)=B.windowSector (by omega) A.geometry.mesh
--           (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell))
--       (hf : ∀ l, B.AlignedSmallSupported (f l))
--       (hcontrol : ∀ l, SmallControlled B.c (f l) (B.windowSector (by omega) A.geometry.mesh
--         (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell))) :
--       Nonempty (B.LocalPatchTemplate (by omega) F f)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.clippedSlopePrimitive`, `OAI.SimpleAmenable.coordinatePrimitive`, `OAI.SimpleAmenable.endpointLabel`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ResolvedBy`, `OAI.SimpleAmenable.coordinateTestIndex`, `OAI.SimpleAmenable.slopeDirection` and `OAI.SimpleAmenable.slopeTestIndex` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.commonVertexDenominator`, `OAI.SimpleAmenable.spatialTranslate`, `OAI.SimpleAmenable.InitialCoverSystem.LocalPatchTemplate`, `OAI.SimpleAmenable.InitialCoverSystem.PrimitiveFamilyLaw`, `OAI.SimpleAmenable.InitialCoverSystem.fullGeometricSector`, `OAI.SimpleAmenable.InitialCoverSystem.primitiveTests` and `OAI.SimpleAmenable.InitialCoverSystem.windowSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.ConcurrentGeometryData` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas` and `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas` (definitions bundle `OAIQ65Sa013` of this split); `OAI.SimpleAmenable.windowRectangle` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_oneSlope_formal_table`, `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_primitive_table_with_coordinates` and `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.translated_slope_coordinate_formal_law` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ConstantCellTemplates.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template)

import Mathlib
import Definitions.Def_OAIQ65Sa013
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section SlopeCoordinateCellTemplate
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas)

theorem slope_coordinate_cell_template {κ : Type} [Finite κ] {J : Type*}
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d j : Fin 2) (v : CutRing × CutRing)
    (P : Fin 2 → κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P i))
    (i₀ i₁ : κ) (hP : P 0 i₀=(slopeTestIndex d,0)) (hQ : P 1 i₁=(coordinateTestIndex j,v))
    (F : Option (Fin 2) → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hF : ∀ i, F (some i)=B.fullGeometricSector (by omega) (P i) (h i)
      (![clippedSlopePrimitive a r (slopeDirection d),spatialTranslate v (coordinatePrimitive a j)] i))
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin A.geometry.mesh)
    (hb : ∀ k, q k ≤ endpointLabel (-r) ∧ endpointLabel (-r)<q k+A.geometry.mesh)
    (he : ∀ k, q k ≤ endpointLabel r ∧ endpointLabel r<q k+A.geometry.mesh)
    (hW : ∀ i, ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r) (P i) s).val)
      (windowRectangle a A.geometry.mesh q cell).val)
    (hcoherent : ∀ i, B.fullGeometricSector (by omega) (P i) (h i)
      (windowRectangle a A.geometry.mesh q cell)=B.windowSector (by omega) A.geometry.mesh
        (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell))
    (hf : ∀ l, B.AlignedSmallSupported (f l))
    (hcontrol : ∀ l, SmallControlled B.c (f l) (B.windowSector (by omega) A.geometry.mesh
      (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell))) :
    Nonempty (B.LocalPatchTemplate (by omega) F f) := by
  sorry

end InitialCoverSystem.PatchAtlas
end SlopeCoordinateCellTemplate

end SimpleAmenable
end
end

end OAI
end
