-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_union_list_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:37:42.030804+00:00
-- url     : https://prove2.me/theorems/a7f13cee-45f3-45db-a37c-54f5b6cd9d8a
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/FiniteMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/FiniteMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext`, with `open WordOperations WordList RationalLeaves`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma union_list_pack_s238r {m : ℕ} (S : Finset (Label (Fin m))) (xs : List (Label (Fin m))) :
--       union (pairBits (setBits S,labels xs))=setBits (S∪xs.toFinset)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.labels` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.count_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/FiniteMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L024
import Definitions.Def_Q238L025

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )
lemma union_list_pack_s238r {m : ℕ} (S : Finset (Label (Fin m))) (xs : List (Label (Fin m))) :
    union (pairBits (setBits S,labels xs))=setBits (S∪xs.toFinset) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end
