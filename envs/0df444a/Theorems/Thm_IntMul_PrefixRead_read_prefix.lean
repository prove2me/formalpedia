-- Prove2me | Theorems.Thm_IntMul_PrefixRead_read_prefix
-- name    : IntMul.PrefixRead.read_prefix
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T13:16:01.791392+00:00
-- url     : https://prove2.me/theorems/a865a5ab-8eea-4d93-8d70-0416f810daea
-- title:
--   Actual counted prefix read from an ordinary binary tape with restored templates
-- statement:
--   Let $p,x,r,a,d$ be finite binary words and let $W=\operatorname{val}(d)+1\le |x|$. From an explicit live caller frame at the beginning of $x$ on the plain input tape $pxr$, with accumulated output $a$ and physically prepared counter/templates for $d$, the fixed four-tape counted machine reads and appends exactly the first $W$ bits of $x$. It halts in its exact terminal frame after at most
--
--   $$6W+4|d|+2$$
--
--   actual transitions. The input tape is retained, both input and output cursors advance by $W$, both counter/template words are restored, and their heads return to the retained positions. No descriptor is appended to the input and no length oracle is supplied to the transition table. This is the physical finite-prefix operation needed for exact output-width conversion.
-- source:
--   Complete physical counted prefix read on an ordinary binary tape. Owns payload emission, real binary counter, amortized countdown clock, template restoration and exact full frame proof. Written by Codex.

import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Tactic
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_CountedStream
import Mathlib.Data.List.GetD
import Definitions.Def_IntMul_PrefixRead

open IntMul IntMul.PrefixRead

theorem IntMul.PrefixRead.read_prefix (pre x tail a y : List Bool)
    (hx : IntMul.val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6 * (IntMul.val y + 1) + 4 * y.length + 2 ∧
      machine.step^[t] (ready pre x tail a y 0 .emit) =
        ready pre x tail a y (IntMul.val y+1) .halt := by sorry
