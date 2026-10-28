-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_formalRectangleMasks
-- name    : OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:34:52.700014+00:00
-- url     : https://prove2.me/theorems/eac55611-276b-4b8c-b55d-3c684323cca5
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalGridPieces.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalGridPieces.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem formalRectangleMasks (hlarge : 15 < m+1)
--       (P : ι → Fin 5 × (CutRing × CutRing)) (T : FormalStarTable (A.starFamily hlarge P))
--       (v : κ → ι)
--       (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
--       (W : D → polygonAlgebra a)
--       (hW : ∀ d, ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (P ∘ v) i).val) (W d).val)
--       (hcover : ∀ x, ∃ d, x ∈ (W d).val)
--       (hd : Pairwise fun d e => Disjoint (W d).val (W e).val) :
--       ∃ C : D → Set (ι → Bool),
--         (Pairwise fun d e => Disjoint (C d) (C e)) ∧
--         (∀ σ, ∃ d, σ ∈ C d) ∧
--         (∀ d, T.sector (C d)=B.fullGeometricSector hlarge (P ∘ v) h (W d)) ∧
--         (∀ d, T.sector (C d)ᶜ=B.fullGeometricSector hlarge (P ∘ v) h (W d)ᶜ) ∧
--         (∀ x d, polygonAssignment (primitiveTests (a := a) (r := r) P) x ∈ C d ↔ x ∈ (W d).val)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonAssignment`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ResolvedBy` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.InitialCoverSystem.PrimitiveFamilyLaw`, `OAI.SimpleAmenable.InitialCoverSystem.fullGeometricSector` and `OAI.SimpleAmenable.InitialCoverSystem.primitiveTests` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.FormalStarTable` and `OAI.SimpleAmenable.FormalStarTable.sector` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas` (definitions bundle `OAIQ65Sa013` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.starFamily` (definitions bundle `OAIQ65Sa015` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.primitive_laws_eventually` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalGridPieces.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks)

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

section PrimitiveRectangleMasks
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι κ D : Type*} [Finite ι] [Finite κ] [Nonempty D]

theorem formalRectangleMasks (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (T : FormalStarTable (A.starFamily hlarge P))
    (v : κ → ι)
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (W : D → polygonAlgebra a)
    (hW : ∀ d, ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (P ∘ v) i).val) (W d).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (hd : Pairwise fun d e => Disjoint (W d).val (W e).val) :
    ∃ C : D → Set (ι → Bool),
      (Pairwise fun d e => Disjoint (C d) (C e)) ∧
      (∀ σ, ∃ d, σ ∈ C d) ∧
      (∀ d, T.sector (C d)=B.fullGeometricSector hlarge (P ∘ v) h (W d)) ∧
      (∀ d, T.sector (C d)ᶜ=B.fullGeometricSector hlarge (P ∘ v) h (W d)ᶜ) ∧
      (∀ x d, polygonAssignment (primitiveTests (a := a) (r := r) P) x ∈ C d ↔ x ∈ (W d).val) := by
  sorry

end InitialCoverSystem.PatchAtlas
end PrimitiveRectangleMasks

end SimpleAmenable
end
end

end OAI
end
