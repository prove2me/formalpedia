-- Prove2me | Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_window_safe
-- name    : IntMul.TrackedBankCleanup.cleanup_window_safe
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:52:01.46257+00:00
-- url     : https://prove2.me/theorems/cb21014a-5cd9-4f92-abda-3e493c9d6b6f
-- title:
--   Protected work-bank boundaries throughout every physical cleanup phase
-- statement:
--   For initialized tracked banks with unique local markers and blank tails beyond their tracked extents, every work head remains at or above its original bank offset at every physical time of cleanup, including all rewind, erasure, restoration and local-marker-erasure transitions, and every later halted step. The statement allows arbitrary retained ancestor prefixes, bank offsets, extents and initial head positions. It proves the complete intermediate trajectory bound, rather than only endpoint preservation.
-- source:
--   Original all-times tracked bank cleanup window invariant. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup
import Mathlib.Tactic

open IntMul IntMul.TrackedBankCleanup

theorem IntMul.TrackedBankCleanup.cleanup_window_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∀ t j, offset j ≤ ((machine M).step^[t]
      (rewindFrame M base offset extent c pos)).head (BankedSimulation.workTape M j) := by sorry
