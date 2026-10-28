-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_primitive_family_global_templates
-- name    : OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:38:58.00376+00:00
-- url     : https://prove2.me/theorems/ac002fe6-4179-401e-9885-ed586084045c
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/PrimitiveGlobalTemplates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/PrimitiveGlobalTemplates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas`, with `open scoped symmDiff`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem primitive_family_global_templates {ι : Type*} [Finite ι]
--       (ha : 0<a) (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
--       (P : ι → Fin 5 × (CutRing × CutRing))
--       (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
--       ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
--       StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
--       (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) ∧
--       ∃ n : ℕ, ∃ q : Fin 2 → ℤ,
--       (∀ cell : Fin 2 → Fin N,
--         ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
--           (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val) ∧
--       ∀ (cell : Fin 2 → Fin N) (J : Type)
--         (f : J → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
--       (∀ v, B.AlignedSmallSupported (f v)) →
--       (∀ v, SmallControlled B.c (f v) (B.windowSector (by omega) n (A.rectangles.rectangles n) q
--         (refinedGridRectangle a N e cell))) →
--       ∃ L : B.LocalPatchTemplate (by omega) (A.starFamily (by omega) P) f,
--         ∀ x : GenericSquare a, x ∈ L.margin.val →
--           polygonAssignment L.predicates x ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.cutTau`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonAssignment`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ResolvedBy` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.commonVertexDenominator`, `OAI.SimpleAmenable.coordinateWindowPrimitives`, `OAI.SimpleAmenable.InitialCoverSystem.LocalPatchTemplate`, `OAI.SimpleAmenable.InitialCoverSystem.primitiveTests` and `OAI.SimpleAmenable.InitialCoverSystem.windowSector` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.ConcurrentGeometryData` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas` and `OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas` (definitions bundle `OAIQ65Sa013` of this split); `OAI.SimpleAmenable.refinedGridRectangle` (definitions bundle `OAIQ65Sa014` of this split); `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.starFamily` (definitions bundle `OAIQ65Sa015` of this split).
--
--   **Used by.** The proofs of `OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_primitive_family_law_all` and `OAI.SimpleAmenable.primitive_laws_eventually` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/PrimitiveGlobalTemplates.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates)

import Mathlib
import Definitions.Def_OAIQ65Sa015

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem primitive_family_global_templates {ι : Type*} [Finite ι]
    (ha : 0<a) (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
    StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) ∧
    ∃ n : ℕ, ∃ q : Fin 2 → ℤ,
    (∀ cell : Fin 2 → Fin N,
      ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val) ∧
    ∀ (cell : Fin 2 → Fin N) (J : Type)
      (f : J → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
    (∀ v, B.AlignedSmallSupported (f v)) →
    (∀ v, SmallControlled B.c (f v) (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (refinedGridRectangle a N e cell))) →
    ∃ L : B.LocalPatchTemplate (by omega) (A.starFamily (by omega) P) f,
      ∀ x : GenericSquare a, x ∈ L.margin.val →
        polygonAssignment L.predicates x ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) := by
  sorry

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
end
