-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_BarrierMenu_matching_expectation_covariance
-- name    : OAI.SimpleAmenable.BarrierMenu.matching_expectation_covariance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T04:16:15.790609+00:00
-- url     : https://prove2.me/theorems/0fd4d262-b768-4839-bd94-8ddeb19c9fb6
-- title:
--   OAI.SimpleAmenable.BarrierMenu.matching_expectation_covariance: intermediate lemma from OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleAmenable.BarrierMenu.matching_expectation_covariance` of [lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/PolygonMatchingLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/PolygonMatchingLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleAmenable.BarrierMenu`, with `open scoped symmDiff`, `open scoped commutatorElement`, `open scoped commutatorElement`, `open Classical MeasureTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem matching_expectation_covariance {η κ : ℝ} {n : ℕ}
--       (hQ : M.Q < sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
--       (g : polygonFullGroup a m) (hg : g∈F) {δ : ℝ}
--       (hc : ObservableClose (jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha)
--         M.signals.eight (commonVertexDenominator_pos ha) η κ n)
--         ((jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
--           (commonVertexDenominator_pos ha) η κ n).map (barrierBitsTransport g)) δ)
--       (f : polygonFullGroup a m → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) :
--       let μ := jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
--         (commonVertexDenominator_pos ha) η κ n
--       |(∫b,matchingAverage (M.signals.sampledPartition n b) f ∂μ)-
--         (∫b,matchingAverage (M.signals.sampledPartition n b) (fun x => f (g*x)) ∂μ)| ≤
--         2*μ.real {b | ¬jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b}+2*δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.SimpleAmenable.TrackPoint` and `OAI.SimpleAmenable.polygonFullGroup` (definitions bundle `OAIQ65Sa001` of this split); `OAI.SimpleAmenable.ObservableClose` and `OAI.SimpleAmenable.sourceDyadicN` (definitions bundle `OAIQ65Sa002` of this split); `OAI.SimpleAmenable.BarrierBits`, `OAI.SimpleAmenable.BarrierMenu`, `OAI.SimpleAmenable.FlagSite`, `OAI.SimpleAmenable.barrierEightDirections`, `OAI.SimpleAmenable.commonVertexDenominator`, `OAI.SimpleAmenable.commonVertexDenominator_pos` and `OAI.SimpleAmenable.BarrierSignalSystem.eight` (definitions bundle `OAIQ65Sa005` of this split); `OAI.SimpleAmenable.barrierBitsTransport` (definitions bundle `OAIQ65Sa009` of this split); `OAI.SimpleAmenable.BarrierSignalSystem.sampledPartition` (definitions bundle `OAIQ65Sa010` of this split); `OAI.SimpleAmenable.jointBitFieldLaw`, `OAI.SimpleAmenable.jointFieldSuccess` and `OAI.SimpleAmenable.matchingAverage` (definitions bundle `OAIQ65Sa014` of this split).
--
--   **Used by.** The proof of `OAI.SimpleAmenable.polygonFullGroup_finiteTestReiter` of this split imports it.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/PolygonMatchingLaw.lean (declaration OAI.SimpleAmenable.BarrierMenu.matching_expectation_covariance)

import Mathlib
import Definitions.Def_OAIQ65Sa014

section

attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonMatchingLaw
open Classical MeasureTheory Filter Set
open scoped Topology

namespace BarrierMenu
variable {a m : ℕ} {ha : 0 < a} {F : Finset (polygonFullGroup a m)} (M : BarrierMenu a m ha F)

theorem matching_expectation_covariance {η κ : ℝ} {n : ℕ}
    (hQ : M.Q < sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
    (g : polygonFullGroup a m) (hg : g∈F) {δ : ℝ}
    (hc : ObservableClose (jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha)
      M.signals.eight (commonVertexDenominator_pos ha) η κ n)
      ((jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
        (commonVertexDenominator_pos ha) η κ n).map (barrierBitsTransport g)) δ)
    (f : polygonFullGroup a m → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) :
    let μ := jointBitFieldLaw (a:=a) (m:=m) (barrierEightDirections ha) M.signals.eight
      (commonVertexDenominator_pos ha) η κ n
    |(∫b,matchingAverage (M.signals.sampledPartition n b) f ∂μ)-
      (∫b,matchingAverage (M.signals.sampledPartition n b) (fun x => f (g*x)) ∂μ)| ≤
      2*μ.real {b | ¬jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b}+2*δ := by
  sorry

end BarrierMenu

end PolygonMatchingLaw

end SimpleAmenable
end
end

end OAI
end
