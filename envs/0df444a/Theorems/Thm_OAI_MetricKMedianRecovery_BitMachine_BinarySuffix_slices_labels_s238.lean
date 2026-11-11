-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySuffix_slices_labels_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:51:59.197871+00:00
-- url     : https://prove2.me/theorems/2544cfb8-4da0-46ef-ab46-5f09dfa1e08d
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/SuffixMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/SuffixMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySuffix`, with `open WordOperations WordList RationalLeaves`, `open BinaryFiniteContext (labels)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma slices_labels_s238 {m : ℕ} (U : List (Label (Fin m))) :
--       Slices.run (labels U)=Slices.outBits BinaryLabel.encode (CanonicalMergeRefinement.cuts U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.cuts` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.labels` and `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.outBits` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run` (definitions bundle `Q238K030` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryJump_expand_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryResolve_view_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/SuffixMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels)

import Mathlib
import Definitions.Def_Q238K030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field )
lemma slices_labels_s238 {m : ℕ} (U : List (Label (Fin m))) :
    Slices.run (labels U)=Slices.outBits BinaryLabel.encode (CanonicalMergeRefinement.cuts U) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end
