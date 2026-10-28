-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_independent_actual_patching
-- name    : OAI.SimpleAmenable.InitialCoverSystem.independent_actual_patching
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:18:20.357985+00:00
-- url     : https://prove2.me/theorems/42c7b1bf-13b1-4c9e-ba24-c0f2031079e9
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.independent_actual_patching: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.independent_actual_patching` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ClosedLocalAssignments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ClosedLocalAssignments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem independent_actual_patching (hlarge : 25 ≤ m+1)
--       (F : (i : Option ι) → Option (κ i) → TrackStar (Fin (m+1)) →*
--         BoundedRelationCover M (alternatingGenerator a r m hm))
--       (T : ∀ i, FormalStarTable (F i)) (U : (i : Option ι) → Set (κ i → Bool))
--       (C : (i : Option ι) → D → Set (κ i → Bool))
--       (hF : ∀ i j, B.AlignedSmallSupported (F i j))
--       (hc : ∀ i, F i none=B.c.comp (universalProjection _))
--       (hd : ∀ i, Pairwise fun d e => Disjoint (C i d) (C i e))
--       (hcover : ∀ i σ, ∃ d, σ ∈ C i d)
--       (j k : D → TrackStar (Fin (m+1)) →*
--         BoundedRelationCover M (alternatingGenerator a r m hm))
--       (hj : ∀ i d, (T i).sector (C i d)=j d)
--       (hk : ∀ i d, (T i).sector (C i d)ᶜ=k d)
--       (hjs : ∀ d, B.AlignedSmallSupported (j d))
--       (hcomm : ∀ d s t, Commute (j d s) (k d t))
--       (hzero : formalGridInput F T U none=B.c.comp (universalProjection _))
--       (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
--         BoundedRelationCover M (alternatingGenerator a r m hm))
--       (hspec : ∀ I i, (formalGridInput F T U i).comp (universalMap (subtypeAlternatingHom I.val))=
--         (f I i).comp (universalProjection (alternatingGroup I.val)))
--       (R : ι → polygonAlgebra a)
--       (L : ∀ d, B.LocalPatchTemplate (by omega)
--         (formalGridInput F T U) (formalGridPiece F T U C d))
--       (hreal : ∀ d x, x ∈ (L d).margin.val →
--         polygonAssignment (L d).predicates x ∈ Set.range (polygonAssignment R)) :
--       HasCentralLaw (smallFamilyModel (actualTestMask R)) (smallFamilyEval f).rangeRestrict
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonAssignment`, `OAI.SimpleAmenable.polygonFullGroup`, `OAI.SimpleAmenable.shortRelations`, `OAI.SimpleAmenable.universalMap` and `OAI.SimpleAmenable.universalProjection` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.FiveAlphabet`, `OAI.SimpleAmenable.HasCentralLaw`, `OAI.SimpleAmenable.SmallFamilyLabel`, `OAI.SimpleAmenable.SmallFamilyWord`, `OAI.SimpleAmenable.fiveSubalphabet_perfect`, `OAI.SimpleAmenable.smallFamilyEval` and `OAI.SimpleAmenable.subtypeAlternatingHom` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.actualTestMask`, `OAI.SimpleAmenable.smallFamilyModel` and `OAI.SimpleAmenable.InitialCoverSystem.LocalPatchTemplate` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.FormalStarTable`, `OAI.SimpleAmenable.FormalStarTable.sector` and `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.formalGridInput` and `OAI.SimpleAmenable.formalGridPiece` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_primitive_family_law_all` and `OAI.SimpleAmenable.primitive_laws_eventually` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/ClosedLocalAssignments.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.independent_actual_patching)

import Mathlib
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section IndependentActualPatching
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι D : Type*} [Finite ι] [Fintype D]
    {κ : Option ι → Type*} [∀ i, Finite (κ i)]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem independent_actual_patching (hlarge : 25 ≤ m+1)
    (F : (i : Option ι) → Option (κ i) → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (T : ∀ i, FormalStarTable (F i)) (U : (i : Option ι) → Set (κ i → Bool))
    (C : (i : Option ι) → D → Set (κ i → Bool))
    (hF : ∀ i j, B.AlignedSmallSupported (F i j))
    (hc : ∀ i, F i none=B.c.comp (universalProjection _))
    (hd : ∀ i, Pairwise fun d e => Disjoint (C i d) (C i e))
    (hcover : ∀ i σ, ∃ d, σ ∈ C i d)
    (j k : D → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hj : ∀ i d, (T i).sector (C i d)=j d)
    (hk : ∀ i d, (T i).sector (C i d)ᶜ=k d)
    (hjs : ∀ d, B.AlignedSmallSupported (j d))
    (hcomm : ∀ d s t, Commute (j d s) (k d t))
    (hzero : formalGridInput F T U none=B.c.comp (universalProjection _))
    (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hspec : ∀ I i, (formalGridInput F T U i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (R : ι → polygonAlgebra a)
    (L : ∀ d, B.LocalPatchTemplate (by omega)
      (formalGridInput F T U) (formalGridPiece F T U C d))
    (hreal : ∀ d x, x ∈ (L d).margin.val →
      polygonAssignment (L d).predicates x ∈ Set.range (polygonAssignment R)) :
    HasCentralLaw (smallFamilyModel (actualTestMask R)) (smallFamilyEval f).rangeRestrict := by
  sorry

end InitialCoverSystem
end IndependentActualPatching

end SimpleAmenable
end
end

end OAI
end
