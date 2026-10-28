-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_BarrierSignalSystem_chart_line_transport
-- name    : OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T03:41:29.610492+00:00
-- url     : https://prove2.me/theorems/0fa10038-f1fa-47a7-8aee-a0f4ec7a4044
-- title:
--   OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport` of [lean/OAI/GroupTheory/SimpleAmenable/Amenability/ChartLineTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Amenability/ChartLineTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.BarrierSignalSystem`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical Set`):
--
--   ```lean
--   theorem chart_line_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
--       (T : Finset PlaneCut)
--       (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
--         fullGroupAffineData g i p=fullGroupAffineData g i q) (p : GenericSquare a)
--       (u : CutRing×CutRing) (hdata : fullGroupAffineData g i p=(k,u))
--       (hQ : 0 ≤ Q)
--       (hB : ∀l ∈ T ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
--         |conjugate (l.2+integralCutForm a l.1 u)| ≤ B)
--       {N : ℝ} (hN : 1 ≤ N) (j : Fin 4) (c : CutRing)
--       (hc : c ∈ barrierCandidate a j N)
--       (hc' : c+integralCutForm a j u ∈ barrierCandidate a j N)
--       (b₁ b₂ b₁' b₂' : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
--       (hs : signalSuccess (flagMeanSignal S.first.signal N) b₁)
--       (hs' : signalSuccess (flagMeanSignal S.first.signal N) b₁')
--       (hb₁ : ∀z,b₁' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ z)
--       (hb₂ : ∀z,b₂' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ z)
--       {x : ℝ} (hx : barrierLinePoint a j c x ∈ openSquareChart T p) :
--       x ∈ subdivisionBarrier (barrierSubdivision ha i j c
--           (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁)) (barrierActivation ha i j c b₂) ↔
--       x+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
--         subdivisionBarrier (barrierSubdivision ha k j (c+integralCutForm a j u)
--           (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁'))
--           (barrierActivation ha k j (c+integralCutForm a j u) b₂')
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.CutRing`, `OAI.SimpleAmenable.GenericSquare`, `OAI.SimpleAmenable.TrackPoint`, `OAI.SimpleAmenable.conjugate`, `OAI.SimpleAmenable.integralCutForm`, `OAI.SimpleAmenable.ordinary` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.barrierLineParameter`, `OAI.SimpleAmenable.signalSuccess`, `OAI.SimpleAmenable.subdivisionBarrier` and `OAI.SimpleAmenable.FieldSignalData.signal` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.BarrierSignalSystem`, `OAI.SimpleAmenable.FlagSite`, `OAI.SimpleAmenable.PlaneCut`, `OAI.SimpleAmenable.barrierCandidate`, `OAI.SimpleAmenable.barrierFlagDirection`, `OAI.SimpleAmenable.barrierLinePoint`, `OAI.SimpleAmenable.commonVertexDenominator`, `OAI.SimpleAmenable.commonVertexDenominator_pos`, `OAI.SimpleAmenable.flagSiteAction`, `OAI.SimpleAmenable.fullGroupAffineData`, `OAI.SimpleAmenable.squareBoundaryCuts`, `OAI.SimpleAmenable.squareSign` and `OAI.SimpleAmenable.BarrierSignalSystem.marks` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.openSquareChart` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.barrierActivation` and `OAI.SimpleAmenable.barrierSubdivision` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.flagMeanSignal` (definitions bundle `OAIQ65Sa011` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.BarrierMenu.sampledPartition_arrow` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Amenability/ChartLineTransport.lean (declaration OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport)

import Mathlib
import Definitions.Def_OAIQ65Sa009
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
section ChartLineTransport
open Classical Set
namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem chart_line_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p : GenericSquare a)
    (u : CutRing×CutRing) (hdata : fullGroupAffineData g i p=(k,u))
    (hQ : 0 ≤ Q)
    (hB : ∀l ∈ T ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
      |conjugate (l.2+integralCutForm a l.1 u)| ≤ B)
    {N : ℝ} (hN : 1 ≤ N) (j : Fin 4) (c : CutRing)
    (hc : c ∈ barrierCandidate a j N)
    (hc' : c+integralCutForm a j u ∈ barrierCandidate a j N)
    (b₁ b₂ b₁' b₂' : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b₁)
    (hs' : signalSuccess (flagMeanSignal S.first.signal N) b₁')
    (hb₁ : ∀z,b₁' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ z)
    (hb₂ : ∀z,b₂' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ z)
    {x : ℝ} (hx : barrierLinePoint a j c x ∈ openSquareChart T p) :
    x ∈ subdivisionBarrier (barrierSubdivision ha i j c
        (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁)) (barrierActivation ha i j c b₂) ↔
    x+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      subdivisionBarrier (barrierSubdivision ha k j (c+integralCutForm a j u)
        (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁'))
        (barrierActivation ha k j (c+integralCutForm a j u) b₂') := by
  sorry

end BarrierSignalSystem
end ChartLineTransport

end SimpleAmenable
end
end

end OAI
end
