-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryProgram_Carried_accepted_frontend
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:30:59.151492+00:00
-- url     : https://prove2.me/theorems/75afad26-9457-42a9-b6d7-8d13059610bf
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried`, with `open OAI BitProgram StructuredCalls HighQueryAdapter`, `open HashGreedyProgram.NativeRound`, `open SqrtLog.ProgramTapeReplay`):
--
--   ```lean
--   theorem accepted_frontend (k : ℕ) : AvoidsCmd H (HighMarkedFrontend.acceptedCommand k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.words` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay.AvoidsCmd` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend.acceptedCommand` (definitions bundle `OAIQ081S183` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.accepted` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S183

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

open HashGreedyProgram.NativeRound

namespace Carried

open SqrtLog.ProgramTapeReplay

local notation "H" => (fun i : Fin 896 => i ∈ words)

theorem accepted_frontend (k : ℕ) : AvoidsCmd H (HighMarkedFrontend.acceptedCommand k) := by
  sorry

attribute [local irreducible] HashMarkedReturn.upperClear

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end
