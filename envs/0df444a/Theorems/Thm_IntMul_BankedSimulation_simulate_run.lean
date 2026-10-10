-- Prove2me | Theorems.Thm_IntMul_BankedSimulation_simulate_run
-- name    : IntMul.BankedSimulation.simulate_run
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T20:41:49.32599+00:00
-- url     : https://prove2.me/theorems/c94560b3-aa9e-416b-b3e1-7f7216174834
-- title:
--   Exact work-bank subroutine simulation with preserved caller tapes and prefixes
-- statement:
--   For every multitape subroutine M, arbitrary outer base configuration, positive bank offsets, child configuration whose cell-zero start markers are intact, and step count T, the single literal bank simulator performs exactly T outer transitions and reaches precisely the embedded T-step child configuration. The complete global input and output tape contents and heads stay equal to the base configuration. Every work-tape cell before its bank offset, including the outer global marker cell, is preserved. This is a generic exact execution compiler for prepared banks, not a free bank-initialization, head-seek, dispatch, or recursive scheduling operation.
-- source:
--   Original literal compiler foundation for the integer-multiplication campaign's clocked recursive multiplier and fixed-tape routing. Written by Codex.

import Definitions.Def_IntMul_BankedSimulation
import Mathlib.Tactic

open IntMul IntMul.BankedSimulation

theorem IntMul.BankedSimulation.simulate_run (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (marker : ∀ j, c.cells j 0 = M.startSym) :
    let final := (machine M).step^[T] (embed M base offset c)
    final = embed M base offset (M.step^[T] c) ∧
      (∀ i : Fin (M.k + 2), i.val < 2 →
        final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j : Fin M.k, ∀ p : ℕ, p < offset j →
        final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j : Fin M.k, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) := by sorry
