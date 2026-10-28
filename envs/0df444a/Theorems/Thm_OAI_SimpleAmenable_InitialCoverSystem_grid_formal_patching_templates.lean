-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_grid_formal_patching_templates
-- name    : OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:43:20.828104+00:00
-- url     : https://prove2.me/theorems/f4f0d302-683c-48f5-b27d-2de21876c882
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CrossingCellActions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CrossingCellActions.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem grid_formal_patching_templates {ι D : Type*} [Finite ι] [Fintype D]
--       {κ : Option ι → Type*} [∀ i, Finite (κ i)]
--       (hlarge : 25 ≤ m+1)
--       (Q : (i : Option ι) → κ i → Fin 5 × (CutRing × CutRing))
--       (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
--       (U : Option ι → polygonAlgebra a) (W : D → polygonAlgebra a)
--       (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
--       (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
--       (he : ∀ i d, B.fullGeometricSector (by omega) (Q i) (h i) (W d)=
--         B.fullGeometricSector (by omega) (Q none) (h none) (W d))
--       (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val)
--       (hcover : ∀ x, ∃ d, x ∈ (W d).val)
--       (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
--         BoundedRelationCover M (alternatingGenerator a r m hm))
--       (hspec : ∀ I i, (B.gridInput (by omega) Q h U i).comp (universalMap (subtypeAlternatingHom I.val))=
--         (f I i).comp (universalProjection (alternatingGroup I.val)))
--       (hconst : U none=wholePolygon a)
--       (hlocal : ∀ d, Nonempty (B.LocalPatchTemplate (by omega)
--         (B.gridInput (by omega) Q h U) (B.gridPiece (by omega) Q h U W d))) :
--       HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
--         (smallFamilyEval f).rangeRestrict
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup`, `OAI.SimpleAmenable.shortRelations`, `OAI.SimpleAmenable.universalMap`, `OAI.SimpleAmenable.universalProjection` and `OAI.SimpleAmenable.wholePolygon` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.FiveAlphabet`, `OAI.SimpleAmenable.HasCentralLaw`, `OAI.SimpleAmenable.ResolvedBy`, `OAI.SimpleAmenable.SmallFamilyLabel`, `OAI.SimpleAmenable.SmallFamilyWord`, `OAI.SimpleAmenable.fiveSubalphabet_perfect`, `OAI.SimpleAmenable.smallFamilyEval` and `OAI.SimpleAmenable.subtypeAlternatingHom` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.smallFamilyModel`, `OAI.SimpleAmenable.InitialCoverSystem.LocalPatchTemplate`, `OAI.SimpleAmenable.InitialCoverSystem.PrimitiveFamilyLaw`, `OAI.SimpleAmenable.InitialCoverSystem.fullGeometricSector` and `OAI.SimpleAmenable.InitialCoverSystem.primitiveTests` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.InitialCoverSystem.gridInput` and `OAI.SimpleAmenable.InitialCoverSystem.gridPiece` (definitions bundle `OAIQ65Sa008` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_oneSlope_formal_table` and `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.translated_slope_coordinate_formal_law` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/CrossingCellActions.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates)

import Mathlib
import Definitions.Def_OAIQ65Sa008

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section LocalPatchTemplates
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι J : Type*}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

attribute [instance] LocalPatchTemplate.finite_index

theorem grid_formal_patching_templates {ι D : Type*} [Finite ι] [Fintype D]
    {κ : Option ι → Type*} [∀ i, Finite (κ i)]
    (hlarge : 25 ≤ m+1)
    (Q : (i : Option ι) → κ i → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
    (U : Option ι → polygonAlgebra a) (W : D → polygonAlgebra a)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : ∀ i d, B.fullGeometricSector (by omega) (Q i) (h i) (W d)=
      B.fullGeometricSector (by omega) (Q none) (h none) (W d))
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hspec : ∀ I i, (B.gridInput (by omega) Q h U i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (hconst : U none=wholePolygon a)
    (hlocal : ∀ d, Nonempty (B.LocalPatchTemplate (by omega)
      (B.gridInput (by omega) Q h U) (B.gridPiece (by omega) Q h U W d))) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict := by
  sorry

end InitialCoverSystem
end LocalPatchTemplates

end SimpleAmenable
end
end

end OAI
end
