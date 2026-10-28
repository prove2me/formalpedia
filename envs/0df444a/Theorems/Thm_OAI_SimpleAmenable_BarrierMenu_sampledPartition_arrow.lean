-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_BarrierMenu_sampledPartition_arrow
-- name    : OAI.SimpleAmenable.BarrierMenu.sampledPartition_arrow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:16:28.793648+00:00
-- url     : https://prove2.me/theorems/adc189e9-4710-46ff-a549-1d09d08fd8e7
-- title:
--   OAI.SimpleAmenable.BarrierMenu.sampledPartition_arrow: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.BarrierMenu.sampledPartition_arrow` of [lean/OAI/GroupTheory/SimpleAmenable/Amenability/FinitePartitionArrows.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Amenability/FinitePartitionArrows.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.BarrierMenu`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical Set`):
--
--   ```lean
--   theorem sampledPartition_arrow {n : ℕ} (hN : 1 ≤ sourceDyadicN n)
--       (hQ : M.Q < sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
--       (g : polygonFullGroup a m) (hg : g∈F) (b : BarrierBits a m ha)
--       (hs : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b)
--       (hs' : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n (barrierBitsTransport g b)) :
--       PartitionArrow (M.signals.sampledPartition n b)
--         (M.signals.sampledPartition n (barrierBitsTransport g b)) g
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.sourceDyadicN` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.BarrierBits`, `OAI.SimpleAmenable.BarrierMenu`, `OAI.SimpleAmenable.barrierEightDirections`, `OAI.SimpleAmenable.commonVertexDenominator` and `OAI.SimpleAmenable.BarrierSignalSystem.eight` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.barrierBitsTransport` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.PartitionArrow` and `OAI.SimpleAmenable.BarrierSignalSystem.sampledPartition` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.jointFieldSuccess` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.BarrierMenu.matching_expectation_covariance` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Amenability/FinitePartitionArrows.lean (declaration OAI.SimpleAmenable.BarrierMenu.sampledPartition_arrow)

import Mathlib
import Definitions.Def_OAIQ65Sa014

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

section SampledPartitionMotion
open Classical Set

namespace BarrierMenu
variable {a m : ℕ} {ha : 0 < a} {F : Finset (polygonFullGroup a m)} (M : BarrierMenu a m ha F)

theorem sampledPartition_arrow {n : ℕ} (hN : 1 ≤ sourceDyadicN n)
    (hQ : M.Q < sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
    (g : polygonFullGroup a m) (hg : g∈F) (b : BarrierBits a m ha)
    (hs : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b)
    (hs' : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n (barrierBitsTransport g b)) :
    PartitionArrow (M.signals.sampledPartition n b)
      (M.signals.sampledPartition n (barrierBitsTransport g b)) g := by
  sorry

end BarrierMenu
end SampledPartitionMotion

end SimpleAmenable
end
end

end OAI
end
