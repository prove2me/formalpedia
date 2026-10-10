-- Prove2me | Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
-- name    : IntMul.TrackedBankPreparation.setup_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T22:43:33.103636+00:00
-- url     : https://prove2.me/theorems/2bcec93b-c3fc-4027-bb65-d56ee177d59d
-- title:
--   Complete physical tracked-bank setup with exact 2*inputLength+3 clock
-- statement:
--   For arbitrary interior buffer/bank offsets, caller prefixes, and caller-computed x#y input, exactly 2*(length(x)+length(y)+1)+3 actual transitions of one fixed four-state M.k+2-tape machine write every local marker, physically copy the full child input while erasing the buffer, initialize precisely the visited-prefix flags, rewind the child input head and halt in the complete prepared tracked M.initCfg frame. The input bank is visited through its entire payload; other child banks have only their local marker visited; all child heads are at their bank offsets. The caller buffer is now empty after its marker with head at its original input end; all older prefixes and root input/head remain unchanged. The source includes unique-marker, blank-tail, head and workspace initialization facts needed by child execution and later cleanup. Input generation and fresh-suffix allocation remain separate obligations.
-- source:
--   Original physical tracked-bank copy-and-erase preparation for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedBankPreparation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul IntMul.TrackedBankPreparation

theorem IntMul.TrackedBankPreparation.setup_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) :
    (machine M).step^[2 * (inputWord M x y).length + 3]
      (initialFrame M base sigma offset x y) = readyFrame M base sigma offset x y := by sorry
