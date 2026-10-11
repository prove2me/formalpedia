-- Prove2me | Theorems.Thm_IntMul_FixedOutputWidth_fixed_output_width
-- name    : IntMul.FixedOutputWidth.fixed_output_width
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T13:33:46.314686+00:00
-- url     : https://prove2.me/theorems/ea252f51-8f57-4539-a615-8b6354560a20
-- title:
--   Complete physical exact-width binary output return with restored counters and linear clock
-- statement:
--   Let $w,d$ be finite binary words, and let $W=\operatorname{val}(d)+1\le |w|$. From an explicit prepared caller configuration containing $w$ on output at its end cursor, empty scratch, and the binary counter/templates for $d$, a fixed fifteen-tape machine halts in its exact terminal configuration after at most
--
--   $$11|w|+10W+4|d|+35$$
--
--   physical transitions. Its output is exactly the big-endian binary representation of $\operatorname{val}(w)$ at width $W$, equivalently the low-order $W$ bits with their zero padding retained. Scratch is empty with head zero, both counter/templates and their heads are restored, and every other caller tape and head is retained. All reversals, counted prefix emissions, marker seeks, erasures and six caller returns are included. This supplies the physically charged width conversion required to return block-padded multiplication output at the campaign model's exact twice-input width. Counter preparation remains an explicit caller obligation.
-- source:
--   Original complete physical fixed-width output return. Privately owns native embeddings, exact retained frames, marker seek, counted-prefix handoffs, both erasures, reverse copy, complete clock summation and binary width identity. Written by Codex.

import Definitions.Def_IntMul_FixedOutputWidth
import Mathlib.Tactic
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fin.Tuple.Take

open IntMul IntMul.FixedOutputWidth

theorem IntMul.FixedOutputWidth.fixed_output_width (base : machine.Cfg) (w d : List Bool) (hW : width d ≤ w.length) :
    ∃ t : ℕ, t ≤ 11*w.length+10*width d+4*d.length+35 ∧
      machine.step^[t] (initialFrame base w d)=finalFrame base w d ∧
      (machine.step^[t] (initialFrame base w d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base w d)).cells 1=
        machine.tapeOf ((bin (width d) (val w)).map machine.bitSym) := by sorry
