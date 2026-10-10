-- Prove2me | Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
-- name    : IntMul.TrackedRootInputCopy.copy_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T23:02:00.995626+00:00
-- url     : https://prove2.me/theorems/1ddfecdf-c95b-4bd5-9918-9af5f49fb34d
-- title:
--   Exact native root-input copy and buffer rewind in 2*inputLength+5 transitions
-- statement:
--   From its real native initial x#y configuration, one fixed finite shared-tape program physically copies the entire input word, including separator and any leading zeroes, into output-buffer cells two onward with true flags, preserves the reserved fresh boundary at cell one and all global markers, retains every root-input cell, physically rewinds the buffer head to one, and parks every fresh child work head at one. The exact full configuration is reached in 2*(length(x)+length(y)+1)+5 actual transitions. No prepared input, address oracle, uncharged seeks or uncharged bank allocation are used. This provides the physical starting input layout for the accepted tracked-bank initializer.
-- source:
--   Original physical native root-input bridge for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedRootInputCopy
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
open IntMul.TrackedBankPreparation (inputWord)

open IntMul IntMul.TrackedRootInputCopy

theorem IntMul.TrackedRootInputCopy.copy_correct (M : MultitapeTM) (x y : List Bool) :
    (machine M).step^[2 * (inputWord M x y).length + 5] ((machine M).initCfg x y) =
      finalFrame M x y := by sorry
