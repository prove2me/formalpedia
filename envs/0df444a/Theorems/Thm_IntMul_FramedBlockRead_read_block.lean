-- Prove2me | Theorems.Thm_IntMul_FramedBlockRead_read_block
-- name    : IntMul.FramedBlockRead.read_block
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T10:40:21.465511+00:00
-- url     : https://prove2.me/theorems/40985814-218c-4fd4-9ec2-133dc7e9fa6e
-- title:
--   Actual interior coefficient read with preserved prefixes and reusable counter
-- statement:
--   Let pre, x, tail, a and y be arbitrary binary words. Put L=val(y)+1 and assume L≤|x|. From its specified live incoming frame, the actual fixed four-tape counted-stream machine reads exactly L bits at the interior input cursor immediately following pre. It appends those bits to the existing output a, retains the entire read-only input pre++x++tail#y, and restores both prepared counter templates and heads. It halts at the exact complete frame after some number t of actual transitions with
--
--   $$t\le6L+4|y|+2.$$
--
--   The input head advances from |pre|+1 to |pre|+L+1 and the output head from |a|+1 to |a|+L+1. The bound is independent of the earlier input prefix and existing output length: those data are retained rather than rescanned. Preparing the live incoming cursor and templates is an explicit caller responsibility.
-- source:
--   Original interior full-frame generalization of the counted-stream routine. Privately owns arithmetic, physical decrement, reset and all live block traces. Countdown analysis derives from the pinned Apache-2.0 integer-mult-bounds material attributed in the counted-stream development. Written by Codex.

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Tactic
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_CountedStream
import Mathlib.Data.List.GetD
import Definitions.Def_IntMul_FramedBlockRead

open IntMul IntMul.FramedBlockRead

theorem IntMul.FramedBlockRead.read_block (pre x tail a y : List Bool)
    (hx : IntMul.val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6 * (IntMul.val y + 1) + 4 * y.length + 2 ∧
      machine.step^[t] (ready pre x tail a y 0 .emit) =
        ready pre x tail a y (IntMul.val y+1) .halt := by sorry
