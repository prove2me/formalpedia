-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace.local_stack_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:44:14.74964+00:00
-- url     : https://prove2.me/theorems/fe0da69d-f6d6-4278-845e-2c8b301dbb71
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace.local_stack_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace.local_stack_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StructuredSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StructuredSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace`, with `open BitProgram`):
--
--   ```lean
--   theorem local_stack_bound {r s l : ℕ} (p : Program r s l)
--       {a : Cfg r s l} {steps initialBound : ℕ}
--       (ha : dataBits a ≤ initialBound) :
--       ∀ prefixSteps intermediate, prefixSteps ≤ steps →
--         Trace p prefixSteps a intermediate →
--         ∀ i, (intermediate.stacks i).length ≤ initialBound + steps
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.dataBits` (definitions bundle `OAIQ081S024` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejection_scan_runs_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.command_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.prepareIncidence_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.command_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.staged_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.PadScore.leaf_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.visits_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace.attempt_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.mass_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace.command_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace.prepare_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution.markedReturn_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.advance_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.install_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.prepare_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_head`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.ascend_leaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.setup_rel_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.descend_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.duplicate_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.nonleaf_iteration_masterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.setup_masterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.zero_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StructuredSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace.local_stack_bound)

import Mathlib
import Definitions.Def_OAIQ081S024

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

theorem local_stack_bound {r s l : ℕ} (p : Program r s l)
    {a : Cfg r s l} {steps initialBound : ℕ}
    (ha : dataBits a ≤ initialBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ initialBound + steps := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end
