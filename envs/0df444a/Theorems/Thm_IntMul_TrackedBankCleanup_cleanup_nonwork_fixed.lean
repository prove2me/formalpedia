-- Prove2me | Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_nonwork_fixed
-- name    : IntMul.TrackedBankCleanup.cleanup_nonwork_fixed
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:57:08.888706+00:00
-- url     : https://prove2.me/theorems/e427703c-0f0c-4270-a7f4-0e39d731510d
-- title:
--   Both caller tapes and heads are fixed throughout every cleanup transition
-- statement:
--   Starting from an arbitrary tracked cleanup rewind frame, the two nonwork tapes retain their entire original tape contents and their original head positions at every physical time. This holds without unique-marker, blank-tail or head-position assumptions, and includes every cleanup state and later halted transitions.
-- source:
--   Original all-times cleanup caller-tape invariance. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup
import Mathlib.Tactic

open IntMul IntMul.TrackedBankCleanup

theorem IntMul.TrackedBankCleanup.cleanup_nonwork_fixed (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ) :
    ∀ t i, i.val < 2 →
      ((machine M).step^[t] (rewindFrame M base offset extent c pos)).head i=base.head i ∧
      ((machine M).step^[t] (rewindFrame M base offset extent c pos)).cells i=base.cells i := by sorry
