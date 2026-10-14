-- Prove2me | Theorems.Thm_IntMul_HvdH_crt_conv
-- name    : IntMul.HvdH.crt_conv
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:34:07.995411+00:00
-- url     : https://prove2.me/theorems/6abfb379-162b-444d-9cc7-9f58aea4eed2
-- title:
--   Agarwal–Cooley: CRT turns cyclic convolution on $\mathbb Z/ab$ into 2-D cyclic convolution
-- statement:
--   Let $a,b\ge1$ be coprime, $R$ a commutative ring, and $\phi:\mathbb Z/ab\to\mathbb Z/a\times\mathbb Z/b$ the Chinese remainder ring isomorphism. For $u,v:\mathbb Z/ab\to R$ and every $x\in\mathbb Z/a\times\mathbb Z/b$,
--   $$\sum_{j\in\mathbb Z/ab}u_j\,v_{\phi^{-1}(x)-j}=\sum_{y\in\mathbb Z/a\times\mathbb Z/b}u_{\phi^{-1}(y)}\,v_{\phi^{-1}(x-y)} .$$
--   In words, reindexing by $\phi$ turns a one-dimensional cyclic convolution of length $ab$ into a two-dimensional cyclic convolution of size $a\times b$.
--
--   This is the Agarwal–Cooley step used in §5.3 (proof of Proposition 5.4) of Harvey–van der Hoeven to turn a length $s_1\cdots s_d$ convolution into a $d$-dimensional one.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.4 and 5.3

import Mathlib

namespace IntMul.HvdH
theorem crt_conv {R : Type*} [CommRing R] {a b : ℕ} [NeZero a] [NeZero b]
    (h : Nat.Coprime a b) (u v : ZMod (a * b) → R) (x : ZMod a × ZMod b) :
    ∑ j : ZMod (a * b), u j * v ((ZMod.chineseRemainder h).symm x - j) =
      ∑ y : ZMod a × ZMod b, u ((ZMod.chineseRemainder h).symm y) *
        v ((ZMod.chineseRemainder h).symm (x - y)) := by sorry
end IntMul.HvdH
