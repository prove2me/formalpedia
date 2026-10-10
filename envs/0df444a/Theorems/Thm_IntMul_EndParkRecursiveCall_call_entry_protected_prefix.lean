-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveCall_call_entry_protected_prefix
-- name    : IntMul.EndParkRecursiveCall.call_entry_protected_prefix
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T07:17:11.218991+00:00
-- url     : https://prove2.me/theorems/c1e005d6-075b-4a54-93e5-2d379a2f59c8
-- title:
--   Complete actual recursive call entry with protected physical trajectory
-- statement:
--   Suppose a live parent body requests a recursive call and its output bank contains the canonical child argument packet for finite bit words x and y. Assume tracked blank tails, near heads and positive parent work offsets, caller buffer marker and continuation position. The actual fixed-tape scheduler reaches the exact complete child body frame after physical argument transfer, continuation push, fresh-bank reservation, child preparation and buffer reset. Its clock is bounded by max(output head,old-buffer length+1)+2max(packet length,old-buffer length)+3 packet length+max(reservation distances)+n+16. Every noninput head is at least one at every intermediate physical time, including the child body endpoint. All service transitions and dispatches are charged.
-- source:
--   Original full protected returned-prefix integration in the actual integer multiplication recursive scheduler. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_window_safe
import Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveCall IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankPreparation (inputWord)

theorem IntMul.EndParkRecursiveCall.call_entry_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (live : c.state≠M.qHalt) (call : request c.state=some label)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (near : ∀ j, c.head j≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        3*(inputWord M x y).length+
        span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        childFrame M n request resume base rho sigma offset extent c label x y ∧
      ∀ a, a ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[a]
          (bodyFrame M n request resume base rho sigma offset extent c v)).head i := by sorry
