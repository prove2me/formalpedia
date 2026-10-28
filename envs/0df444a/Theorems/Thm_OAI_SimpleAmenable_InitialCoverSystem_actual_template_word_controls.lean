-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_actual_template_word_controls
-- name    : OAI.SimpleAmenable.InitialCoverSystem.actual_template_word_controls
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:46:36.080981+00:00
-- url     : https://prove2.me/theorems/b1f083c6-337c-4a6f-8b4a-18fcf0b4be46
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.actual_template_word_controls: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.actual_template_word_controls` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/TemplateRelators.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/TemplateRelators.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem actual_template_word_controls (hlarge : 25 ≤ m+1)
--       (P : κ → Fin 5 × (CutRing × CutRing))
--       (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
--       (U : ι → polygonAlgebra a) (V : polygonAlgebra a)
--       (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) P j).val) (U i).val)
--       (hV : ResolvedBy (fun j => (primitiveTests (a := a) (r := r) P j).val) V.val)
--       (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
--       (hf : B.AlignedSmallSupported f)
--       (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h V))
--       (S : Finset (Fin (m+1))) (hS : S.card ≤ 15)
--       (w : SmallFamilyWord (Fin (m+1)) ι) (hw : w ∈ smallFamilyLocal S)
--       (hrel : smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w=1) :
--       ∀ x ∈ f.range, Commute
--         (copyFamilyEval (fun i => B.fullGeometricSector (by omega) P h (marginFamily U V i))
--           (smallFamilyStarWord w)) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.UniversalExtension`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.polygonAlgebra`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ResolvedBy`, `OAI.SimpleAmenable.SmallFamilyLabel`, `OAI.SimpleAmenable.SmallFamilyWord`, `OAI.SimpleAmenable.copyFamilyEval` and `OAI.SimpleAmenable.smallFamilyLocal` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.SmallControlled`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.smallFamilyModel`, `OAI.SimpleAmenable.InitialCoverSystem.PrimitiveFamilyLaw`, `OAI.SimpleAmenable.InitialCoverSystem.fullGeometricSector` and `OAI.SimpleAmenable.InitialCoverSystem.primitiveTests` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.InitialCoverSystem.marginFamily` (definitions bundle `OAIQ65Sa008` of this split); `OAI.SimpleAmenable.smallFamilyStarWord` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.InitialCoverSystem.AlignedSmallSupported` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/TemplateRelators.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.actual_template_word_controls)

import Mathlib
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa011

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ActualTemplateRelators

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem actual_template_word_controls (hlarge : 25 ≤ m+1)
    (P : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U : ι → polygonAlgebra a) (V : polygonAlgebra a)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) P j).val) (U i).val)
    (hV : ResolvedBy (fun j => (primitiveTests (a := a) (r := r) P j).val) V.val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h V))
    (S : Finset (Fin (m+1))) (hS : S.card ≤ 15)
    (w : SmallFamilyWord (Fin (m+1)) ι) (hw : w ∈ smallFamilyLocal S)
    (hrel : smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w=1) :
    ∀ x ∈ f.range, Commute
      (copyFamilyEval (fun i => B.fullGeometricSector (by omega) P h (marginFamily U V i))
        (smallFamilyStarWord w)) x := by
  sorry

end InitialCoverSystem
end ActualTemplateRelators

end SimpleAmenable
end
end

end OAI
end
