-- Prove2me | Theorems.Thm_IntMul_HvdH_log2Bits_bound
-- name    : IntMul.HvdH.log2Bits_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:48:13.235713+00:00
-- url     : https://prove2.me/theorems/f157df0c-ef63-4155-86dd-d6754fae725b
-- title:
--   $n$-bit approximation of $\log 2$
-- statement:
--   For every $n\ge0$ the integer `log2Bits n` (from $\log 2=2\operatorname{artanh}\frac13$ with truncated, floor-rounded series to $2n+9$ bits, then rounded to $n$ bits; see `IntMul_HvdH_Numeric`) satisfies $|\mathrm{log2Bits}(n)-2^n\log 2|\le 1$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.8 (computing pi and log 2 to p bits)

import Definitions.Def_IntMul_HvdH_Numeric

namespace IntMul.HvdH
theorem log2Bits_bound (n : ℕ) : |(log2Bits n : ℝ) - 2 ^ n * Real.log 2| ≤ 1 := by sorry
end IntMul.HvdH
