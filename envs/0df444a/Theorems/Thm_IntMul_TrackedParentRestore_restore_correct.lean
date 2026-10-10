-- Prove2me | Theorems.Thm_IntMul_TrackedParentRestore_restore_correct
-- name    : IntMul.TrackedParentRestore.restore_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T23:33:43.067747+00:00
-- url     : https://prove2.me/theorems/83326d2b-6c28-4b66-94d7-2da902532ce2
-- title:
--   Exact physical parent-head restoration retaining every parent cell and visited flag
-- statement:
--   For tracked parent banks with unique local markers, one fixed finite shared-tape routine restores every work head to its parent boundary in exactly max_j(pos_j)+1 actual transitions. Each bank stops independently when its own head reaches its local marker. The complete terminal configuration retains every parent and ancestor cell and every visited flag, root input, caller output and root/buffer heads. No offset, displacement or extent is read as an external address oracle; the finite transition sees only the scanned local marker. Starting from the reserved child boundary pos_j=E_j+1 gives at most max_j(E_j)+2 transitions. Complete child cleanup must first erase every child marker; child input production and unbounded recursive scheduling remain separate.
-- source:
--   Original physical tracked parent-head restoration for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedParentRestore
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)

open IntMul IntMul.TrackedParentRestore

theorem IntMul.TrackedParentRestore.restore_correct (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) (pos : Fin M.k → ℕ) :
    (machine M).step^[span M pos + 1] (initialFrame M base offset extent c pos) =
      finalFrame M base offset extent c ∧
    (∀ j, (finalFrame M base offset extent c).head (workTape M j) = offset j) := by sorry
