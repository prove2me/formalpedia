-- Prove2me | Theorems.Thm_IntMul_BankedCall_call_correct
-- name    : IntMul.BankedCall.call_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T21:08:32.864391+00:00
-- url     : https://prove2.me/theorems/190718dd-34d2-40af-9de2-5e06933a874b
-- title:
--   Complete literal banked subroutine call: physical setup, exact child execution, and output return
-- statement:
--   For every finite multitape child machine M and every run on x#y that halts with exact output w within T transitions, the fixed banked caller starts from its real outer initial configuration, physically initializes the child banks, runs M, physically rewinds and copies its output, and globally halts with exactly w. The complete returned configuration is proved. Its clock is at most T plus the child's final output-head distance plus |w|+2|x|+2|y|+9. No free bank initialization, input/output head seek, dispatch, or output transfer is assumed. The universal consequence is a 2T+linear bound; if the child returns its output head at O(|w|), the added overhead is linear while the leading child-execution coefficient stays one.
-- source:
--   Original literal compiler foundation for the integer-multiplication campaign's clocked recursive multiplier and fixed-tape routing. Written by Codex.

import Definitions.Def_IntMul_BankedCall
import Theorems.Thm_IntMul_BankedSimulation_simulate_run
import Theorems.Thm_IntMul_BankedCall_setup_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul IntMul.BankedCall

theorem IntMul.BankedCall.call_correct (M : MultitapeTM) (x y : List Bool) (T : ℕ) (w : List Bool)
    (halts : M.HaltsWithOutput x y T w) :
    ∃ t : ℕ,
      t ≤ T + (M.step^[T] (M.initCfg x y)).head M.outTape + w.length +
        2 * x.length + 2 * y.length + 9 ∧
      (machine M).HaltsWithOutput x y t w ∧
      (machine M).step^[t] ((machine M).initCfg x y) =
        finalFrame M x y (M.step^[T] (M.initCfg x y)) w := by sorry
