-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveEvaluation_ordinary_window_safe
-- name    : IntMul.EndParkRecursiveEvaluation.ordinary_window_safe
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:48:18.138242+00:00
-- url     : https://prove2.me/theorems/ebe89db5-e7a0-4d25-80b6-7adc34587eb7
-- title:
--   Protected noninput windows throughout every ordinary recursive body segment
-- statement:
--   For a body initialized with unique local markers and heads no farther than one beyond its tracked extents, every actual scheduler step up to the next call or halt keeps every noninput head at least one, provided the work, buffer and continuation-stack boundaries are positive. The bound holds at every intermediate physical time, including the segment endpoint, and is derived from the actual body transition table rather than assumed as a trajectory condition.
-- source:
--   Original ordinary recursive body protected-window invariant. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveRelocation
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveEvaluation IntMul.EndParkRecursiveScheduler

theorem IntMul.EndParkRecursiveEvaluation.ordinary_window_safe (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (S : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (near : ∀ j, c.head j ≤ extent j+1)
    (live : ∀ s, s < S → (M.step^[s] c).state ≠ M.qHalt)
    (ordinary : ∀ s, s < S → request (M.step^[s] c).state=none) :
    ∀ t, t ≤ S → ∀ i, i ≠ (machine M n request resume).inTape →
      1 ≤ ((machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)).head i := by sorry
