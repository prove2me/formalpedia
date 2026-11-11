-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRows_capRow_one_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:47:51.241462+00:00
-- url     : https://prove2.me/theorems/a69c6bba-1850-4740-8ea0-5a9fd9e4380d
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma capRow_one_s238 (u : Fin n) : capRow 1 (pairBits (data,u.val.bits))=
--       BinaryCompletion.rowBits (RationalSampling.reference δ G Δ ⟨∅,s.leaves⟩ u) (fun e=>δ u (loc e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` and `OAI.MetricKMedianRecovery.RationalSampling.reference` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.rowBits` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.pack` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow` (definitions bundle `Q238K029` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K029

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRows
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n q r : ℕ}
section Correct
variable (δ : Fin n→Fin n→ℚ) (D S G : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (loc : Fin q→Fin n) (red : Fin r→Fin n) (k : ℕ)
local notation "data" => pack δ D S G Δ s loc red k
lemma capRow_one_s238 (u : Fin n) : capRow 1 (pairBits (data,u.val.bits))=
    BinaryCompletion.rowBits (RationalSampling.reference δ G Δ ⟨∅,s.leaves⟩ u) (fun e=>δ u (loc e)) := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

end OAI
end
