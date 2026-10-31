-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryReturnReplay_marked
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:28:05.789121+00:00
-- url     : https://prove2.me/theorems/81be7d70-1804-4d1c-895b-8897409c7c1e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryReturnReplay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryReturnReplay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay`, with `open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay`, `open HashGreedyProgram.NativeRound HighQueryEntryShadow`):
--
--   ```lean
--   theorem marked {k steps count localBound frameBound : ℕ} {input output : Data}
--       (he : Eval (HighQueryProgram.marked k) steps (erase input) output)
--       (hw : HashMassAdapter.workspace output = HashMassAdapter.workspace (erase input))
--       (hp : output.regs 16 = false ∧ output.regs 17 = true ∧ output.regs 18 = false)
--       (h321 : output.stacks 321 = []) (h324 : output.stacks 324 = [])
--       (hcount : output.stacks 323 = countWord count)
--       (hs : StageSpace (HighQueryProgram.marked k) (steps+1) (erase input) localBound)
--       (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
--       Eval (HighQueryProgram.marked k) steps input (restore input output) ∧
--       HashMassAdapter.workspace (restore input output) = HashMassAdapter.workspace input ∧
--       HashMassAdapter.read (restore input output) = HashMassAdapter.read input ∧
--       RecordPrograms.state HashMassAdapter.recordPorts (restore input output)
--         false true false (input.stacks 320) [] = restore input output ∧
--       (restore input output).stacks 323 = countWord count ∧
--       (restore input output).stacks 324 = [] ∧
--       StageSpace (HighQueryProgram.marked k) (steps+1) input (max localBound frameBound)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.words` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.RecordPrograms.state` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.recordPorts` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.NativeRound.StageSpace` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.read` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.workspace` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow.erase`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.restore` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.marked` (definitions bundle `OAIQ081S193` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryReturnReplay.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HashGreedyProgram.NativeRound HighQueryEntryShadow

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

theorem marked {k steps count localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.marked k) steps (erase input) output)
    (hw : HashMassAdapter.workspace output = HashMassAdapter.workspace (erase input))
    (hp : output.regs 16 = false ∧ output.regs 17 = true ∧ output.regs 18 = false)
    (h321 : output.stacks 321 = []) (h324 : output.stacks 324 = [])
    (hcount : output.stacks 323 = countWord count)
    (hs : StageSpace (HighQueryProgram.marked k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    Eval (HighQueryProgram.marked k) steps input (restore input output) ∧
    HashMassAdapter.workspace (restore input output) = HashMassAdapter.workspace input ∧
    HashMassAdapter.read (restore input output) = HashMassAdapter.read input ∧
    RecordPrograms.state HashMassAdapter.recordPorts (restore input output)
      false true false (input.stacks 320) [] = restore input output ∧
    (restore input output).stacks 323 = countWord count ∧
    (restore input output).stacks 324 = [] ∧
    StageSpace (HighQueryProgram.marked k) (steps+1) input (max localBound frameBound) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay
end
