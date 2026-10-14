-- Prove2me | Theorems.Thm_IntMul_HvdH_piBits_bound
-- name    : IntMul.HvdH.piBits_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:47:31.052803+00:00
-- url     : https://prove2.me/theorems/34bcd395-0c4b-4eba-b6e1-742eddf93ee8
-- title:
--   $n$-bit approximation of $\pi$ via Machin's formula
-- statement:
--   For every $n\ge0$ the integer `piBits n` (Machin's formula $\pi=16\arctan\frac15-4\arctan\frac1{239}$ with truncated, floor-rounded series to $2n+9$ bits, then rounded to $n$ bits; see `IntMul_HvdH_Numeric`) satisfies $|\mathrm{piBits}(n)-2^n\pi|\le 1$, i.e. $|\mathrm{piBits}(n)/2^n-\pi|\le2^{-n}$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.8 (computing pi and log 2 to p bits)

import Definitions.Def_IntMul_HvdH_Numeric

namespace IntMul.HvdH
theorem piBits_bound (n : ℕ) : |(piBits n : ℝ) - 2 ^ n * Real.pi| ≤ 1 := by sorry
end IntMul.HvdH
