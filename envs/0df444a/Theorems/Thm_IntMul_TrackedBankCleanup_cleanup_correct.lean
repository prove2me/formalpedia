-- Prove2me | Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
-- name    : IntMul.TrackedBankCleanup.cleanup_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T22:14:07.992491+00:00
-- url     : https://prove2.me/theorems/defb9d67-730e-4e8b-adf1-f6a12c7d0ae5
-- title:
--   Complete physical child-workspace cleanup with exact clock and fresh reusable banks
-- statement:
--   Starting from arbitrary prepared tracked child banks, unique local start markers, initialized blank tails and arbitrary nonnegative bank-head distances, exactly max(head distances)+2*max(visited payload extents)+3 actual machine transitions clear all child bank suffixes and local markers and halt with every work head at its original boundary. The root input and caller buffer cells/heads, all ancestor prefixes and every outer cell-zero marker are preserved. Every bank cell at or beyond its offset is genuinely fresh blank with false visited flag. Smaller banks stop independently during all parallel seeks/sweeps. No ancestor-size scan, numerical address oracle or supplied endmarker is used. This is a clearing contract; output copying, bank preparation and recursive scheduling remain separate obligations.
-- source:
--   Original finite visited-workspace clearing construction for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)

open IntMul IntMul.TrackedBankCleanup

theorem IntMul.TrackedBankCleanup.cleanup_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    let final := (machine M).step^[span M pos + 2 * span M extent + 3]
      (rewindFrame M base offset extent c pos)
    final = finalFrame M base offset ∧
      (∀ i : Fin (M.k + 2), i.val < 2 → final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j p, p < offset j → final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) ∧
      (∀ j p, offset j ≤ p → final.cells (workTape M j) p = some (M.blank,false)) ∧
      (∀ j, final.head (workTape M j) = offset j) := by sorry
