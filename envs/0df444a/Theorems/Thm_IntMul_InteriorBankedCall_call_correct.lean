-- Prove2me | Theorems.Thm_IntMul_InteriorBankedCall_call_correct
-- name    : IntMul.InteriorBankedCall.call_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T21:40:02.283981+00:00
-- url     : https://prove2.me/theorems/5dd4658f-36a3-4e97-9bcc-704dc9ae8487
-- title:
--   Complete charged child call in arbitrary interior banks with saved caller data
-- statement:
--   For any finite child machine M, arbitrary saved caller configuration, input buffer boundary sigma, positive child bank offsets and a child computation on x#y halting within T steps with output w, the literal interior caller reaches its full final frame within T+max(L+1,h)+|w|+2L+6 transitions, where L=|x|+|y|+1 and h is the child terminal output head distance. It physically creates markers, copies and erases the input buffer, rewinds and dispatches the child input, runs the exact child transitions, independently rewinds the buffer and child output, copies the output into the erased buffer and halts. The saved prefixes before every bank/buffer boundary, root input tape and its head are retained. This is a trace from explicitly prepared fresh suffix banks and a caller-computed input buffer, whose creation is a separate charged obligation.
-- source:
--   Original finite-tape compiler foundation for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_InteriorBankedCall
import Theorems.Thm_IntMul_BankedSimulation_simulate_run
import Theorems.Thm_IntMul_InteriorBankedCall_setup_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul IntMul.InteriorBankedCall

theorem IntMul.InteriorBankedCall.call_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (T : ℕ) (w : List Bool) (halts : M.HaltsWithOutput x y T w) :
    ∃ t : ℕ,
      t ≤ T + max ((BankedCall.inputWord M x y).length + 1)
        ((M.step^[T] (M.initCfg x y)).head M.outTape) + w.length +
        2 * (BankedCall.inputWord M x y).length + 6 ∧
      (machine M).step^[t] (inputFrame M base sigma offset x y) =
        finalFrame M base sigma offset x y (M.step^[T] (M.initCfg x y)) w := by sorry
