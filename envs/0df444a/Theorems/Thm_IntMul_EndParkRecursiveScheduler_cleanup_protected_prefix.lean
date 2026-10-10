-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveScheduler_cleanup_protected_prefix
-- name    : IntMul.EndParkRecursiveScheduler.cleanup_protected_prefix
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T06:45:24.834974+00:00
-- url     : https://prove2.me/theorems/0beef646-a09f-481d-8e66-87f453e3039d
-- title:
--   Complete protected cleanup prefix in the actual fixed-tape recursive scheduler
-- statement:
--   Let a tracked cleanup invocation have bank offsets $o_j\ge1$, tracked extents $E_j$, initial relative head positions $p_j$, unique local markers and blank tails. Suppose its retained caller buffer and padded continuation-stack heads are positive. The actual optimized recursive scheduler reaches the exact padded cleaned frame at a physical time $t$ satisfying
--   \[t\le \max_j p_j+2\max_j E_j+3.\]
--   Every noninput head is at least one at every intermediate physical time $s\le t$, including the cleanup service exit. The theorem combines exact endpoint correctness and the complete protected trajectory within one depth-independent fixed-tape transition table. The subsequent scheduler stack-inspection dispatch lies outside this prefix.
-- source:
--   Original integration of full cleanup trajectory invariants into the actual recursive scheduler. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_window_safe
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_nonwork_fixed
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveScheduler

theorem IntMul.EndParkRecursiveScheduler.cleanup_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (padBase : (cleanupMachine M).Cfg) (callerBase : (TrackedBankCleanup.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (positive : ∀ j, 1 ≤ offset j)
    (bufferPositive : 1 ≤ callerBase.head (TrackedBankCleanup.machine M).outTape)
    (stackPositive : 1 ≤ padBase.head (FixedTapeExtension.extraTape (TrackedBankCleanup.machine M)))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ TrackedBankCleanup.span M pos+2*TrackedBankCleanup.span M extent+3 ∧
      (machine M n request resume).step^[t]
        (liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
          padBase (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos)))=
        liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
          padBase (TrackedBankCleanup.finalFrame M callerBase offset)) ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[s]
          (liftCleanup M n request resume (FixedTapeExtension.embed (TrackedBankCleanup.machine M)
            padBase (TrackedBankCleanup.rewindFrame M callerBase offset extent c pos)))).head i := by sorry
