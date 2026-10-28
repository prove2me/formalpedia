-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_naturalAdderConfig_machine_exact
-- name    : OAI.CommonBasesFPRAS.naturalAdderConfig_machine_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T20:50:28.381+00:00
-- url     : https://prove2.me/theorems/706e2335-9af0-46d0-bcf6-466268d9bd89
-- title:
--   Binary addition returns the exact sum at linear cost
-- statement:
--   The fixed call-enabled register program adds any two binary-encoded natural numbers. It returns the exact sum in its output register, clears its scratch register, does not halt or query the oracle, and uses at most six times the larger input width plus ten bit operations.
-- source:
--   This theorem combines the published binary-adder continuation simulation with the Nat.bits input bridge and the exact linear operation count.

import Definitions.Def_OAICommonBasesFPRASNaturalAdderMachine

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem OAI.CommonBasesFPRAS.naturalAdderConfig_machine_exact {n : ℕ} (O : IndependenceOracle n)
    (coins : ℕ → Bool) (a b : ℕ) :
    let c := naturalAdderConfig a b
    let out := execution
      (binaryStackAdderWithCall (fun _ => Instruction.halt) ⟨0, by omega⟩)
      O c coins (adderTotalSteps a.bits b.bits + 1)
    out.control = ⟨23, by omega⟩ ∧
    binaryValue (out.registers (adderReg 6)) = a + b ∧
    out.registers (adderReg 7) = [true] ∧
    out.registers (adderReg 8) = [] ∧
    out.output = none ∧ out.oracleCalls = 0 ∧
    out.bitOperations ≤ 6 * max a.bits.length b.bits.length + 10 := by
  sorry
