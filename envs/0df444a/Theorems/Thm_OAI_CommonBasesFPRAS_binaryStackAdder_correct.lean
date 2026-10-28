-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_binaryStackAdder_correct
-- name    : OAI.CommonBasesFPRAS.binaryStackAdder_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T03:29:30.310533+00:00
-- url     : https://prove2.me/theorems/3b8c96cf-b767-439f-ad4c-af486e8e49c6
-- title:
--   Correctness and exact cost of the binary stack adder
-- statement:
--   The fixed stack program halts with the exact sum of any two finite binary inputs, makes no oracle calls, and uses an explicit number of machine bit operations including the final output write.
-- source:
--   Lean 4.33.1 reusable machine-arithmetic contribution to the existing Approximate counting of common bases of two matroids mission. This fixed stack program is an arithmetic component, not the estimator implementation.

import Definitions.Def_OAICommonBasesFPRASBinaryStackAdder
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem OAI.CommonBasesFPRAS.binaryStackAdder_correct
    (O : OAI.CommonBasesFPRAS.IndependenceOracle 0) (bits : ℕ → Bool)
    (c : OAI.CommonBasesFPRAS.MachineConfig 2 21) (a b : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = OAI.CommonBasesFPRAS.adderState 0)
    (hleft : c.registers (OAI.CommonBasesFPRAS.adderReg 6) = a)
    (hright : c.registers (OAI.CommonBasesFPRAS.adderReg 7) = b)
    (hscratch : c.registers (OAI.CommonBasesFPRAS.adderReg 8) = []) :
    let out := OAI.CommonBasesFPRAS.execution OAI.CommonBasesFPRAS.binaryStackAdder
      O c bits (OAI.CommonBasesFPRAS.adderTotalSteps a b)
    out.control = OAI.CommonBasesFPRAS.adderState 21 ∧
    out.output = some (((OAI.CommonBasesFPRAS.binaryValue a +
      OAI.CommonBasesFPRAS.binaryValue b : ℕ) : ℚ)) ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 * max a.length b.length +
      OAI.CommonBasesFPRAS.adderCarrySteps a b +
      2 * (OAI.CommonBasesFPRAS.adderFinalScratch a b).length +
      (OAI.CommonBasesFPRAS.addBitsAux false a b).length + 4
  := by
  sorry
