-- Prove2me | Theorems.Thm_LL_Decomp368b_primorial_c3
-- name    : LL_Decomp368b.primorial_c3
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-18T00:55:31.193862+00:00
-- url     : https://prove2.me/theorems/3f423a79-bba0-4936-8b9f-183426bbc34b
-- title:
--   Primorial bound $n\#\cdot25^n<68^n$ for $4\cdot10^6<n\le8\cdot10^6$
-- statement:
--   For every natural number $n$ with $4000000<n\le8000000$, the primorial $n\#=\prod_{p\le n,\ p\text{ prime}}p$ satisfies $n\#\cdot25^n<68^n$. Equivalently, $\theta(n)<n\log(68/25)$ on this range, where $\theta(n)=\sum_{p\le n}\log p$.
-- source:
--   Derived from Schoenfeld, Math. Comp. 30, 1976, 337-360, p. 356, display 5.1*; used in Liu and Wang, Acta Arith. 105, 2002, 133-175.

import Mathlib

namespace LL_Decomp368b
theorem primorial_c3 (n : ℕ) (hn : 4000000 < n) (hn' : n ≤ 8000000) :
    primorial n * 25 ^ n < 68 ^ n := by sorry
end LL_Decomp368b
