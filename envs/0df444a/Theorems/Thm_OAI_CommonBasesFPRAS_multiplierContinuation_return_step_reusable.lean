-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_multiplierContinuation_return_step_reusable
-- name    : OAI.CommonBasesFPRAS.multiplierContinuation_return_step_reusable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T21:10:11.348784+00:00
-- url     : https://prove2.me/theorems/b94f57c8-cb17-4f97-8c81-39c08ec9cc7b
-- title:
--   Multiplier return preserves its machine state
-- statement:
--   Suppose a fixed binary-stack multiplier has reached its return boundary, has not produced an output, and its marker stack is empty. Replacing the terminal halt by a return instruction advances to the continuation in one step, preserves all registers and the oracle-call count, and charges exactly one bit operation.
-- source:
--   The continuation wrapper reuses the accepted binary multiplier and defines a one-step pop from its empty marker stack to the continuation entry.

import Definitions.Def_OAICommonBasesFPRASMultiplierContinuation

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem OAI.CommonBasesFPRAS.multiplierContinuation_return_step_reusable {s n : ℕ}
    (P : Program 2 s) (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 (s + 38))
    (hcontrol : c.control = ⟨36, by omega⟩)
    (hout : c.output = none) (hmarker : c.registers (adderReg 3) = []) :
    let out := execution (binaryStackMultiplierWithCall P) O c bits 1
    out.control = ⟨38, by omega⟩ ∧ out.registers = c.registers ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 1 := by
  sorry
