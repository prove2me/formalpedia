-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_ConcurrentGeometry_InwardChart_refined_cells_locally_decided
-- name    : OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.refined_cells_locally_decided
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:17:20.554394+00:00
-- url     : https://prove2.me/theorems/a136fd9a-14af-4634-a901-cf3bddeb13d5
-- title:
--   OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.refined_cells_locally_decided: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.refined_cells_locally_decided` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/RefinedLocalDecisions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/RefinedLocalDecisions.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem refined_cells_locally_decided (hr : 0<ordinary r ∧ ordinary r<1/2) :
--       ∃ δ : ℝ, 0<δ ∧ ∀ (N : ℕ) (e : Fin (N+1) → CutRing),
--       StrictMono (fun i => ordinary (e i)) → e 0=0 → e (Fin.last N)=1 →
--       (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) →
--       ∀ cell : Fin 2 → Fin N,
--       (∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
--         |ordinary (e (cell k).succ)-realCoordinate z k|<δ) →
--       ∀ p : GenericSquare a, p ∈ (refinedGridRectangle a N e cell).val →
--         p ∈ (C.inwardMargin T.vertex T.offset z).val ∧
--         ∀ i, p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
--           p ∈ (cutPolygon a (j i) (c i)).val
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.ordinary` and `OAI.SimpleAmenable.polygonAlgebra` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.realCoordinate` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.ConcurrentGeometry`, `OAI.SimpleAmenable.cutPolygon`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart`, `OAI.SimpleAmenable.ConcurrentGeometry.inwardMargin`, `OAI.SimpleAmenable.ConcurrentGeometry.localDecision`, `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.offset` and `OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.vertex` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.refinedGridRectangle` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proofs of `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_local_templates`, `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_germ_action_neighborhood` and `OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.refined_clipped_model_action_neighborhood` of this split import it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/RefinedLocalDecisions.lean (declaration OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.refined_cells_locally_decided)

import Mathlib
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section RefinedLocalDecisions

namespace ConcurrentGeometry.InwardChart
variable {a : ℕ} {r : CutRing} {C : ConcurrentGeometry a r} {ι : Type*} [Finite ι]
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem refined_cells_locally_decided (hr : 0<ordinary r ∧ ordinary r<1/2) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (N : ℕ) (e : Fin (N+1) → CutRing),
    StrictMono (fun i => ordinary (e i)) → e 0=0 → e (Fin.last N)=1 →
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) →
    ∀ cell : Fin 2 → Fin N,
    (∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ) →
    ∀ p : GenericSquare a, p ∈ (refinedGridRectangle a N e cell).val →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧
      ∀ i, p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val := by
  sorry

end ConcurrentGeometry.InwardChart
end RefinedLocalDecisions

end SimpleAmenable
end
end

end OAI
end
