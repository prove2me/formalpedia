-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_sampler_positions_cover_tape
-- name    : OAI.CommonBasesFPRAS.sampler_positions_cover_tape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:30:50.187254+00:00
-- url     : https://prove2.me/theorems/521f6619-1485-40ba-90ec-98d3621d5646
-- title:
--   Exact finite positions for the sampler tape
-- statement:
--   The sampler reads K distinct fair-bit positions, all within 3K+1 steps, and stores exactly those bits in the finite-list order consumed by the source estimator.
-- source:
--   Lean 4.33.1 sampler implementation bridge; depends on the proved exact sampler/evaluator simulation.

import Definitions.Def_CountingMatroidProgramShift
import Theorems.Thm_OAI_CommonBasesFPRAS_sampleThen_afterSampling
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The finite sampler reads distinct tape coordinates, and its stack records those bits in the same order as the chosen finite sample. -/
theorem OAI.CommonBasesFPRAS.sampler_positions_cover_tape {s n : ℕ}
    (P : OAI.CommonBasesFPRAS.Program 2 s)
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n)
    (c : OAI.CommonBasesFPRAS.MachineConfig 2 s)
    (bits : ℕ → Bool) (K : ℕ) (hreg9 : c.registers 9 = []) :
    ∃ positions : Fin K ↪ Fin (3*K+1),
      (∀ i, (positions i).val = 3 * (K - 1 - i.val) + 1) ∧
      (OAI.CommonBasesFPRAS.execution
        (OAI.CommonBasesFPRAS.sampleThenProgram P) O
        (OAI.CommonBasesFPRAS.sampledProgramConfig c bits K 0)
        bits (3*K+1)).registers 9 =
        List.ofFn (fun i : Fin K => bits (positions i).val) := by
  sorry
