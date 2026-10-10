-- Prove2me | Theorems.Thm_IntMul_TapeStack_push_correct
-- name    : IntMul.TapeStack.push_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T21:44:58.077344+00:00
-- url     : https://prove2.me/theorems/09fa442a-01d8-4291-bf48-4f14636440ad
-- title:
--   Physical stack push and source erasure in 2n+2 steps independent of ancestors
-- statement:
--   For every saved configuration, local source/stack/scratch boundaries and binary word w, the literal four-tape stack machine pushes w into the fresh parked suffix, appends its delimiter, physically erases the source and restores the source head in exactly 2|w|+2 transitions. Equality of full configurations is proved. The root input, older stack prefix, source prefix and entire prepared temporary tape are retained; no older frame is scanned. Empty words and arbitrary boundary positions are included. Prepared source, local separators and fresh suffixes are explicit frame preconditions; their creation is a separate caller task.
-- source:
--   Original actual one-way MultitapeTM formalization of the fixed-control stack push/pop strategy in CrocSwap/integer-mult-bounds research/machine-transfer-verification/transfer-proof/tapes/TapeStack*.lean, pinned at 3b6b66891c0ac888521cf591fe306c6286601d4f. Written by Codex.

import Definitions.Def_IntMul_TapeStack
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul IntMul.TapeStack

theorem IntMul.TapeStack.push_correct (base : machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    machine.step^[2 * w.length + 2] (pushFrame base sigma rho tau w 0) =
      pushDoneFrame base sigma rho tau w := by sorry
