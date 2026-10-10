-- Prove2me | Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_prefix_safe
-- name    : IntMul.TrackedBankCleanup.cleanup_prefix_safe
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:54:24.394058+00:00
-- url     : https://prove2.me/theorems/e01efcf5-5f54-4f2d-8ad6-8f98167cd0f3
-- title:
--   Every ancestor work-bank prefix is preserved at every actual cleanup time
-- statement:
--   For tracked banks initialized with unique local markers and blank tails beyond their tracked extents, every cell strictly before each work-bank offset retains its original ancestor symbol at every physical cleanup time. The statement covers all rewind, erasure, restoration, marker-erasure and later halted steps, arbitrary bank positions and arbitrary retained ancestor prefixes.
-- source:
--   Original all-times physical cleanup ancestor-prefix preservation. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup
import Mathlib.Tactic

open IntMul IntMul.TrackedBankCleanup

theorem IntMul.TrackedBankCleanup.cleanup_prefix_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∀ t j p, p < offset j → ((machine M).step^[t]
      (rewindFrame M base offset extent c pos)).cells (BankedSimulation.workTape M j) p=
        base.cells (BankedSimulation.workTape M j) p := by sorry
