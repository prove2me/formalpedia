-- Prove2me | Theorems.Thm_LL_Decomp551a_primorial_c5_upper_second
-- name    : LL_Decomp551a.primorial_c5_upper_second
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-17T15:40:17.65039+00:00
-- url     : https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4
-- title:
--   Primorial bound $n\#\cdot25^n<68^n$ for $2.8\cdot10^7<n\le3.2\cdot10^7$
-- statement:
--   For every natural number $n$ with $28000000<n\le32000000$, the primorial $n\#=\prod_{p\le n,\ p\text{ prime}}p$ satisfies $n\#\cdot25^n<68^n$. Equivalently, $\theta(n)<n\log(68/25)$ on this range, where $\theta(n)=\sum_{p\le n}\log p$.
-- source:
--   Derived from Schoenfeld, Math. Comp. 30, 1976, 337-360, p. 356, display 5.1*; used in Liu and Wang, Acta Arith. 105, 2002, 133-175.

import Mathlib

namespace LL_Decomp551a
theorem primorial_c5_upper_second (n : ℕ) (hn : 28000000 < n) (hn' : n ≤ 32000000) :
    primorial n * 25 ^ n < 68 ^ n := by sorry
end LL_Decomp551a
