-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_binaryStackAdder_cost_le
-- name    : OAI.CommonBasesFPRAS.binaryStackAdder_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T03:47:14.661402+00:00
-- url     : https://prove2.me/theorems/6733ccbd-b36b-40dc-b86d-8a7264477c37
-- title:
--   Linear bit-operation bound for binary stack addition
-- statement:
--   The fixed binary stack adder computes the sum of two little-endian inputs in at most six times the wider input bit length plus ten bit operations, in addition to the starting counter. The estimate follows from the exact execution theorem and the fact that the carry and output stacks grow by at most one bit. This is a reusable cost bound for composing arithmetic routines in the counting estimator compiler.
-- source:
--   Lean 4.33.1 cost-bound lemma for the existing Approximate counting of common bases of two matroids mission. Imports and uses the already proved fixed binary stack adder theorem.

import Definitions.Def_OAICommonBasesFPRASBinaryStackAdder
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem OAI.CommonBasesFPRAS.binaryStackAdder_cost_le
    (O : OAI.CommonBasesFPRAS.IndependenceOracle 0) (bits : ℕ → Bool)
    (c : OAI.CommonBasesFPRAS.MachineConfig 2 21) (a b : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = OAI.CommonBasesFPRAS.adderState 0)
    (hleft : c.registers (OAI.CommonBasesFPRAS.adderReg 6) = a)
    (hright : c.registers (OAI.CommonBasesFPRAS.adderReg 7) = b)
    (hscratch : c.registers (OAI.CommonBasesFPRAS.adderReg 8) = []) :
    (OAI.CommonBasesFPRAS.execution OAI.CommonBasesFPRAS.binaryStackAdder
      O c bits (OAI.CommonBasesFPRAS.adderTotalSteps a b)).bitOperations ≤
      c.bitOperations + 6 * max a.length b.length + 10
  := by
  sorry
