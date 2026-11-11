-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:43.536838+00:00
-- url     : https://prove2.me/theorems/7e387968-91fc-4fa2-b0c2-76e6753f2af6
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack7.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack7.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial`, with `open BinaryArithmetic`, `open WordList`):
--
--   ```lean
--   lemma indices_replicate_s238 (n : ℕ) : indices (List.replicate n true)=WordList.encode (List.ofFn (fun i : Fin n=>i.val.bits))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices` and `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_matrix_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteMachine_continuation_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteMachine_initial_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.algorithm_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryInputParser_Metric_matrix_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.run_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.demand_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_demandWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalSearch_step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.clients_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.P.facilities_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sumWords_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseAdvance_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.updatedBudget_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.rowCoefficients_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryResolve_view_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.atPrefix_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Trace_input_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Trace.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack7.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate)

import Mathlib
import Definitions.Def_Q238K001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open BinaryArithmetic
namespace BinaryEllipsoidInitial
open WordList

lemma indices_replicate_s238 (n : ℕ) : indices (List.replicate n true)=WordList.encode (List.ofFn (fun i : Fin n=>i.val.bits)) := by
  sorry

end BinaryEllipsoidInitial
end
open BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end
