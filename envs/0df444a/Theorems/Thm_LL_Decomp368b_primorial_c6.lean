-- Prove2me | Theorems.Thm_LL_Decomp368b_primorial_c6
-- name    : LL_Decomp368b.primorial_c6
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-18T00:55:54.980376+00:00
-- url     : https://prove2.me/theorems/a0f4179e-aba1-4440-a678-cf5f4c829b20
-- title:
--   Primorial bound $n\#\cdot25^n<68^n$ for $3.2\cdot10^7<n\le10^8$
-- statement:
--   For every natural number $n$ with $32000000<n\le100000000$, the primorial $n\#=\prod_{p\le n,\ p\text{ prime}}p$ satisfies $n\#\cdot25^n<68^n$. Equivalently, $\theta(n)<n\log(68/25)$ on this range, where $\theta(n)=\sum_{p\le n}\log p$.
-- source:
--   Derived from Schoenfeld, Math. Comp. 30, 1976, 337-360, p. 356, display 5.1*; used in Liu and Wang, Acta Arith. 105, 2002, 133-175.

import Mathlib

namespace LL_Decomp368b
theorem primorial_c6 (n : ℕ) (hn : 32000000 < n) (hn' : n ≤ 100000000) :
    primorial n * 25 ^ n < 68 ^ n := by sorry
end LL_Decomp368b
