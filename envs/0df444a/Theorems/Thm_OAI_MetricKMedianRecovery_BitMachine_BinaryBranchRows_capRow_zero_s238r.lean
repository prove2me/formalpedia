-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRows_capRow_zero_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:37:12.054608+00:00
-- url     : https://prove2.me/theorems/837120aa-3a75-4ff4-8c55-014e8952e49c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma capRow_zero_s238r (u : Fin n) : capRow 0 (pairBits (data,u.val.bits))=
--       BinaryCompletion.rowBits (RationalSampling.reference δ S Δ s u) (fun e=>δ u (loc e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` and `OAI.MetricKMedianRecovery.RationalSampling.reference` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.rowBits` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow` and `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L019
import Definitions.Def_Q238L024

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
lemma capRow_zero_s238r (u : Fin n) : capRow 0 (pairBits (data,u.val.bits))=
    BinaryCompletion.rowBits (RationalSampling.reference δ S Δ s u) (fun e=>δ u (loc e)) := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchRows

end OAI
end
