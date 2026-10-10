-- Prove2me | Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
-- name    : IntMul.TrackedOutputShift.shift_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T23:09:46.211908+00:00
-- url     : https://prove2.me/theorems/7bcb7a59-12cb-4319-a3e3-d67d2a691c6d
-- title:
--   Exact returned-buffer shift and temporary-marker erase in 4*outputLength+4 transitions
-- statement:
--   For any caller configuration and returned word w in the local buffer beginning at cell two after its marker at one, with buffer head at length(w)+2, one fixed finite shared-tape machine performs exactly 4*length(w)+4 actual transitions and halts in the full native output frame. Every bit is physically shifted left to cells one onward, the local marker is overwritten or erased and the last duplicate is erased, with fresh blank tail and head at length(w)+1. Global cell zero is retained; when it contains the native marker, the resulting tape is exactly the native tapeOf w. Every other tape cell and head is unchanged. Empty output and arbitrary leading zeroes are included.
-- source:
--   Original physical finite-register native output placement for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedOutputShift
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.TrackedOutputShift

theorem IntMul.TrackedOutputShift.shift_correct (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) :
    (machine M).step^[4 * w.length + 4] (rewindFrame M base w (w.length + 2)) =
      finalFrame M base w := by sorry
