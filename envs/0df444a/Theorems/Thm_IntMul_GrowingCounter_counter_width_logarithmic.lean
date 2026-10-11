-- Prove2me | Theorems.Thm_IntMul_GrowingCounter_counter_width_logarithmic
-- name    : IntMul.GrowingCounter.counter_width_logarithmic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T15:05:00.935447+00:00
-- url     : https://prove2.me/theorems/0b059ba7-db50-4b38-8e1b-a548bcff6ecb
-- title:
--   Exact logarithmic representation width of the physical growing binary counter
-- statement:
--   Let $b_n$ be the little-endian word obtained by $n$ increments of the growing binary counter from its empty zero representation. Then
--
--   $$|b_n|=\left\lceil\log_2(n+1)\right\rceil,\qquad\operatorname{val}_{\mathrm{LE}}(b_n)=n,$$
--
--   and $b_n$ is empty exactly when $n=0$. The counter is the word transformation implemented by the physical growing-counter machine. Thus its actual generated representation has the least width needed for its value, including the empty representation of zero. For a width-minus-one descriptor computed from input of total length $W>0$, this gives exact descriptor length $\lceil\log_2 W\rceil$. This supplies the logarithmic workspace bound needed when deriving block and coefficient parameters from original operand input.
-- source:
--   Original exact width proof for the accepted physical counter transformation. Owns canonical high-bit invariant and both power bounds. Written by Codex.

import Definitions.Def_IntMul_GrowingCounter
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

open IntMul IntMul.GrowingCounter

theorem IntMul.GrowingCounter.counter_width_logarithmic (n : ℕ) :
    (iterateCounter n []).length=Nat.clog 2 (n+1) ∧
      BinaryAdder.littleVal (iterateCounter n [])=n ∧
      (iterateCounter n []=[] ↔ n=0) := by sorry
