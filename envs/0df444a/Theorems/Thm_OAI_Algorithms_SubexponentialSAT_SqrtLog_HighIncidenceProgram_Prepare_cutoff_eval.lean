-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HighIncidenceProgram_Prepare_cutoff_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:00:40.605034+00:00
-- url     : https://prove2.me/theorems/f0ae5a0d-6eee-4998-a082-3a79691d0515
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HighIncidenceProgramPrepareOps.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HighIncidenceProgramPrepareOps.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic`):
--
--   ```lean
--   theorem cutoff_eval (d : Data) (hn : 0 < BinaryArithmetic.toNat (d.stacks 16))
--       (hwork : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 → d.stacks (cutoffPorts i) = []) :
--       ∃ time b, Eval cutoffCall time d b ∧
--         time ≤ Cutoff.bound (d.stacks 19) (d.stacks 17) (d.stacks 16) ∧
--         BinaryArithmetic.toNat (b.stacks 20) = (BinaryArithmetic.toNat (d.stacks 19) * BinaryArithmetic.toNat (d.stacks 17)) ⌈/⌉ BinaryArithmetic.toNat (d.stacks 16) ∧
--         (b.stacks 20).length ≤ (d.stacks 19).length + (d.stacks 17).length + 2 ∧
--         (∀ i : Fin 32, i.val < 16 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
--           i = 21 ∨ i = 22 ∨ i = 23 → b.stacks i = d.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff.bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoffPorts` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoffCall` (definitions bundle `OAIQ081S085` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HighIncidenceProgramPrepareOps.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S085

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem cutoff_eval (d : Data) (hn : 0 < BinaryArithmetic.toNat (d.stacks 16))
    (hwork : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 → d.stacks (cutoffPorts i) = []) :
    ∃ time b, Eval cutoffCall time d b ∧
      time ≤ Cutoff.bound (d.stacks 19) (d.stacks 17) (d.stacks 16) ∧
      BinaryArithmetic.toNat (b.stacks 20) = (BinaryArithmetic.toNat (d.stacks 19) * BinaryArithmetic.toNat (d.stacks 17)) ⌈/⌉ BinaryArithmetic.toNat (d.stacks 16) ∧
      (b.stacks 20).length ≤ (d.stacks 19).length + (d.stacks 17).length + 2 ∧
      (∀ i : Fin 32, i.val < 16 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
        i = 21 ∨ i = 22 ∨ i = 23 → b.stacks i = d.stacks i) := by
  sorry

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end
