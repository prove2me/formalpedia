-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_axis_cut_sequence_commutations
-- name    : OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:45:22.281396+00:00
-- url     : https://prove2.me/theorems/6239d2af-a9ae-40e4-9489-012f54aaf41e
-- title:
--   OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations` of [lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/AxisCutCommutation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/AxisCutCommutation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.InitialCoverSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`):
--
--   ```lean
--   theorem axis_cut_sequence_commutations (hlarge : 20 ≤ m+1)
--       (hr : 0 < ordinary r ∧ ordinary r < 1/2)
--       (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
--       (hwz : w*z=1)
--       (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
--       {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
--       (hconj : |conjugate (cutTau^a)| < 1/1000) :
--       ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
--         (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
--         ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
--         ∀ (d : Fin 2) (K : ℕ) (D : AxisCutSequence n K),
--         ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) ≤ C/(n:ℝ) →
--         (∀ i j, |(endpointLabel (D.cut j-D.cut i):ℝ)| ≤ 6*(n:ℝ)/5) →
--         ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1 ∧
--         ∀ i j : ℕ, i ≤ j → ∀ x y,
--           Commute (D.prefixCopy B (by omega) g d i x) (D.suffix B (by omega) g d j y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.BoundedRelationCover`, `OAI.SimpleAmenable.CentralizedFree`, `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.SourceGeneratorLabel`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.alternatingGenerator`, `OAI.SimpleAmenable.centralizingRelations`, `OAI.SimpleAmenable.conjugate`, `OAI.SimpleAmenable.cutTau`, `OAI.SimpleAmenable.endpointLabel`, `OAI.SimpleAmenable.instNormalFreeGroupCentralizingRelations`, `OAI.SimpleAmenable.ordinary`, `OAI.SimpleAmenable.polygonAlternatingGroup`, `OAI.SimpleAmenable.polygonFullGroup` and `OAI.SimpleAmenable.shortRelations` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.AxisCutSequence`, `OAI.SimpleAmenable.InitialCoverSystem`, `OAI.SimpleAmenable.TrackStar`, `OAI.SimpleAmenable.AxisCutSequence.prefixCopy`, `OAI.SimpleAmenable.AxisCutSequence.suffix` and `OAI.SimpleAmenable.InitialCoverSystem.CoordinateWindowLaw` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.symmetricWindowStart` (definitions bundle `OAIQ65Sa008` of this split); `OAI.SimpleAmenable.symmetricWindowLength` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.InitialCoverSystem.TangentChartLaws` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/AxisCutCommutation.lean (declaration OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations)

import Mathlib
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section AxisCutCommutation
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axis_cut_sequence_commutations (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (d : Fin 2) (K : ℕ) (D : AxisCutSequence n K),
      ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) ≤ C/(n:ℝ) →
      (∀ i j, |(endpointLabel (D.cut j-D.cut i):ℝ)| ≤ 6*(n:ℝ)/5) →
      ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1 ∧
      ∀ i j : ℕ, i ≤ j → ∀ x y,
        Commute (D.prefixCopy B (by omega) g d i x) (D.suffix B (by omega) g d j y) := by
  sorry

end InitialCoverSystem
end AxisCutCommutation

end SimpleAmenable
end
end

end OAI
end
