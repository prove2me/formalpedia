-- Prove2me | Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
-- name    : IntMul.TrackedBankedSimulation.simulate_run
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T21:56:25.065018+00:00
-- url     : https://prove2.me/theorems/a30b35ef-6f3e-4694-994c-3eee04ca5b45
-- title:
--   Exact one-step-per-step child execution with tracked workspace and saved caller prefixes
-- statement:
--   For any finite child machine M, arbitrary saved caller configuration, positive bank offsets, initial visited extents and child configuration with local markers and heads at most one beyond their extents, T actual outer transitions yield exactly the full child T-step configuration in the same banks with precisely the updated visited-prefix flags. The root input and caller buffer cells/heads, every work-bank prefix and every outer cell-zero marker are retained. No extra transitions are charged for workspace tracking, and padded halted runs do not mark phantom cells. Initial bank data/flags, bank preparation and later clearing are explicit separate obligations.
-- source:
--   Original finite visited-workspace instrumentation for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedBankedSimulation
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)

open IntMul IntMul.TrackedBankedSimulation

theorem IntMul.TrackedBankedSimulation.simulate_run (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (marker : ∀ j, c.cells j 0 = M.startSym)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    let final := (machine M).step^[T] (embed M base offset extent c)
    final = embed M base offset (extents M c extent T) (M.step^[T] c) ∧
      (∀ i : Fin (M.k + 2), i.val < 2 → final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j : Fin M.k, ∀ p : ℕ, p < offset j →
        final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j : Fin M.k, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) := by sorry
