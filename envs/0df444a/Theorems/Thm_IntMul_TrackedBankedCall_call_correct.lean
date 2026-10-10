-- Prove2me | Theorems.Thm_IntMul_TrackedBankedCall_call_correct
-- name    : IntMul.TrackedBankedCall.call_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T22:51:31.349831+00:00
-- url     : https://prove2.me/theorems/8b4fccb9-8222-4b12-b9b2-121bf9c81b3c
-- title:
--   Complete physical setup, child execution, output return and fresh-bank cleanup with coefficient one on child time
-- statement:
--   Starting with arbitrary saved prefixes, a caller-computed x#y buffer and reserved fresh child suffixes, one fixed finite program physically prepares all tracked child input and markers, executes the child until halt, returns its canonical word and erases every child suffix and local marker, parking all work heads at the original offsets. If T is a valid child halt clock, E is the largest final tracked extent, and L=length(x)+length(y)+1, the complete actual transition bound is T+5E+2L+13. Initial unique-marker, blank-tail and head invariants are derived from real preparation; the input extent automatically bounds the emptied buffer head. All stage switches, flags, markers, copy/erase, rewind, output transfers and cleanup are charged. Root input and saved ancestor prefixes remain intact. Child workspace is explicit; recursive scheduling and caller input generation remain separate.
-- source:
--   Original complete physical tracked interior caller for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankedCall
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedReturnCall_call_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

open IntMul IntMul.TrackedBankedCall

theorem IntMul.TrackedBankedCall.call_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (x y : List Bool) (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 13 ∧
      (machine M).step^[t] (initialFrame M base sigma offset x y) =
        finalFrame M base sigma offset (extents M (M.initCfg x y) (initialExtent M x y) T)
          (M.step^[T] (M.initCfg x y)) w := by sorry
