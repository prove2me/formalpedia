-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_naturalMultiplierConfig_machine_exact
-- name    : OAI.CommonBasesFPRAS.naturalMultiplierConfig_machine_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T20:42:12.465993+00:00
-- url     : https://prove2.me/theorems/c929c92e-2fd0-485a-877f-b126c77b9adf
-- title:
--   Binary multiplication has exact output and quadratic cost
-- statement:
--   One fixed OAI register program multiplies any two binary-encoded natural numbers exactly. On every input it makes zero oracle calls and uses at most 100 times the product of a linear function of the multiplier width and a linear function of the combined operand widths in bit operations.
-- source:
--   The fixed shift-and-add program and its complete machine trace are proved in the published continuation module. This theorem connects the program to the actual Nat.bits input encoding and exposes the exact output and resource bound needed by the estimator schedule compiler.

import Definitions.Def_OAICommonBasesFPRASNaturalMultiplierMachineV2

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem OAI.CommonBasesFPRAS.naturalMultiplierConfig_machine_exact {n : ℕ} (O : IndependenceOracle n)
    (coins : ℕ → Bool) (a b : ℕ) :
    let c := naturalMultiplierConfig a b
    let out := execution binaryStackMultiplierProgram O c coins
      (binaryStackMultiplierLoopSteps [] a.bits b.bits)
    out.output = some ((a * b : ℕ) : ℚ) ∧
      out.oracleCalls = 0 ∧
      out.bitOperations ≤ 100 * (b.bits.length + 1) *
        (a.bits.length + b.bits.length + 5) := by
  sorry
