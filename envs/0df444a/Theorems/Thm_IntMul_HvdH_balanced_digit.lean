-- Prove2me | Theorems.Thm_IntMul_HvdH_balanced_digit
-- name    : IntMul.HvdH.balanced_digit
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:17:32.994409+00:00
-- url     : https://prove2.me/theorems/159c0bd6-c892-4fd6-90ec-f36a4c921514
-- title:
--   Balanced digit extraction: $c=((W+B/2)\bmod B)-B/2$
-- statement:
--   Let $B>0$ be an even integer and let $W=c+BW'$ with $W'\in\mathbb Z$ and $2|c|<B$. Then the low balanced digit $c$ of $W$ is recovered as
--   $$c=\big((W+B/2)\bmod B\big)-B/2 .$$
--   This is the digit-reading step of Kronecker unpacking in Lemma 2.5 of Harvey–van der Hoeven (there $B=2^{3p}$, so $\bmod B$ reads the last $3p$ bits).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.5, Lemma 2.5 (Kronecker substitution)

import Mathlib

namespace IntMul.HvdH
theorem balanced_digit (B : ℤ) (hB : 0 < B) (hBe : Even B) (c W' : ℤ) (hc : 2 * |c| < B) :
    c = (c + B * W' + B / 2) % B - B / 2 := by sorry
end IntMul.HvdH
