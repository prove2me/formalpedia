-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySpace_clear_bank_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace.clear_bank_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T23:43:26.755136+00:00
-- url     : https://prove2.me/theorems/a430a099-7d53-469e-88b3-e520a91f9937
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace.clear_bank_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace.clear_bank_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace`, with `open BitProgram StructuredCalls StackRoutines`):
--
--   ```lean
--   theorem clear_bank_bound {r s : ℕ} (tmp : Fin s) (value present : Fin r)
--       (ports : List (Fin s)) (hp : ports.Nodup) (a : State r s)
--       (hempty : a.stacks tmp=[]) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound)
--       (input output : Fin s) :
--       ∀ (q : ℕ) z,
--         q ≤ 2 * (ports.map (fun i => (a.stacks i).length)).sum + 3 * ports.length + 3 →
--         Trace (compiled (BankRoutines.clearCmd tmp value present ports) input output) q
--           (a.withPC (some (compiled (BankRoutines.clearCmd tmp value present ports) input output).entry)) z →
--         ∀ i, (z.stacks i).length≤bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.BankRoutines.clearCmd` (definitions bundle `OAIQ081S024` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.cost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn.trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStagedSpace.command_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace.prepare_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace.prepare_high_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialize_trace_space` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.trace_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQuerySpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace.clear_bank_bound)

import Mathlib
import Definitions.Def_OAIQ081S024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace

open BitProgram StructuredCalls StackRoutines

theorem clear_bank_bound {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hp : ports.Nodup) (a : State r s)
    (hempty : a.stacks tmp=[]) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound)
    (input output : Fin s) :
    ∀ (q : ℕ) z,
      q ≤ 2 * (ports.map (fun i => (a.stacks i).length)).sum + 3 * ports.length + 3 →
      Trace (compiled (BankRoutines.clearCmd tmp value present ports) input output) q
        (a.withPC (some (compiled (BankRoutines.clearCmd tmp value present ports) input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
end
