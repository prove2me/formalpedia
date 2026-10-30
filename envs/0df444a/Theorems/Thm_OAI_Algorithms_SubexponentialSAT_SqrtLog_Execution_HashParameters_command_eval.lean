-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Execution_HashParameters_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:07:21.315847+00:00
-- url     : https://prove2.me/theorems/98d39754-d840-4068-a134-e257d4e42be5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ExecutionHashParameters.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ExecutionHashParameters.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters`, with `open BitProgram StructuredCalls`):
--
--   ```lean
--   theorem command_eval {R S : ℕ} (p : Ports R S) (a : State R S) (L : ℕ)
--       (hword : SubexpSetupStorage.WordBound L (projectState p.register p.stack a))
--       (hready : HashInputs.Ready (projectState p.hash.register p.hash.stack a))
--       (hm : BinaryArithmetic.toNat (a.stacks (p.stack 15)) ≠ 0) :
--       ∃ t ≤ 10000000000*(L+1)^2+1, ∃ b : State R S,
--         Eval (command p) t a b ∧
--         HashInputs.Ready (projectState p.hash.register p.hash.stack b) ∧
--         BinaryArithmetic.toNat (b.stacks (p.hash.stack 0)) =
--           3*BinaryArithmetic.toNat (a.stacks (p.stack 15)) ∧
--         BinaryArithmetic.toNat (b.stacks (p.hash.stack 5)) =
--           SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks (p.stack 15)))
--             (BinaryArithmetic.toNat (a.stacks (p.stack 16))) ∧
--         BinaryArithmetic.toNat (b.stacks (p.hash.stack 6)) =
--           HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks (p.stack 14)))
--             (BinaryArithmetic.toNat (a.stacks (p.stack 15))) ∧
--         b.stacks (p.hash.stack 9) = a.stacks (p.hash.stack 9) ∧
--         (∀ i, i ∉ HashParametersProgram.ABI.work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 →
--           b.stacks (p.stack i) = a.stacks (p.stack i)) ∧
--         (∀ i, (∀ j, p.stack j ≠ i) → b.stacks i = a.stacks i) ∧
--         (∀ i, (∀ j, p.register j ≠ i) → b.regs i = a.regs i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.Ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.work` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.Hash.Ports` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.Ports.hash` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashInputs.Ready` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.prepareHash_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ExecutionHashParameters.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S106

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Execution.HashParameters

open BitProgram StructuredCalls

theorem command_eval {R S : ℕ} (p : Ports R S) (a : State R S) (L : ℕ)
    (hword : SubexpSetupStorage.WordBound L (projectState p.register p.stack a))
    (hready : HashInputs.Ready (projectState p.hash.register p.hash.stack a))
    (hm : BinaryArithmetic.toNat (a.stacks (p.stack 15)) ≠ 0) :
    ∃ t ≤ 10000000000*(L+1)^2+1, ∃ b : State R S,
      Eval (command p) t a b ∧
      HashInputs.Ready (projectState p.hash.register p.hash.stack b) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 0)) =
        3*BinaryArithmetic.toNat (a.stacks (p.stack 15)) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 5)) =
        SparseCode.distanceDenom (BinaryArithmetic.toNat (a.stacks (p.stack 15)))
          (BinaryArithmetic.toNat (a.stacks (p.stack 16))) ∧
      BinaryArithmetic.toNat (b.stacks (p.hash.stack 6)) =
        HashSelect.loopCap (BinaryArithmetic.toNat (a.stacks (p.stack 14)))
          (BinaryArithmetic.toNat (a.stacks (p.stack 15))) ∧
      b.stacks (p.hash.stack 9) = a.stacks (p.hash.stack 9) ∧
      (∀ i, i ∉ HashParametersProgram.ABI.work → i ≠ 39 → i ≠ 0 → i ≠ 5 → i ≠ 6 →
        b.stacks (p.stack i) = a.stacks (p.stack i)) ∧
      (∀ i, (∀ j, p.stack j ≠ i) → b.stacks i = a.stacks i) ∧
      (∀ i, (∀ j, p.register j ≠ i) → b.regs i = a.regs i) := by
  sorry

end SubexponentialSAT.SqrtLog.Execution.HashParameters

end OAI.Algorithms
end
