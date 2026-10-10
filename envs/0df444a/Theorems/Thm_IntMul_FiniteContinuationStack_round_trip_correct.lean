-- Prove2me | Theorems.Thm_IntMul_FiniteContinuationStack_round_trip_correct
-- name    : IntMul.FiniteContinuationStack.round_trip_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T23:53:20.065101+00:00
-- url     : https://prove2.me/theorems/d027ef6d-0099-41b9-a19e-ebf2987d02db
-- title:
--   Exact physical continuation push/pop recovering the finite return label and restoring all cells and heads
-- statement:
--   Let q be one of n finite continuation labels. From a fresh stack suffix at an arbitrary boundary rho with an arbitrary saved older prefix, the fixed service table physically pushes q, dispatches to pop, recovers q into its finite resume state and erases the complete record in exactly
--   \[2n+4\]
--   actual transitions. Its final state is resume(q), and every tape cell and every head position equals the complete initial frame. Push uses n+1 transitions, the physical push-to-pop dispatch uses one, and pop uses n+2. Older records are retained exactly, while root input, caller buffers and work banks are unchanged throughout. The same finite table works at arbitrary stack depths; n is a fixed control-size parameter. This supplies actual continuation storage and recovery for a later scheduler, rather than a host-language stack or a free return instruction.
-- source:
--   Original physical finite continuation stack for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FiniteContinuationStack
import Mathlib.Tactic

open IntMul IntMul.FiniteContinuationStack

theorem IntMul.FiniteContinuationStack.round_trip_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q) = finalFrame M n base rho q ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).state = .resume q ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).cells =
      (pushStartFrame M n base rho q).cells ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).head =
      (pushStartFrame M n base rho q).head := by sorry
