-- Prove2me | Theorems.Thm_LL_Decomp368b_primorial_c4
-- name    : LL_Decomp368b.primorial_c4
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-18T00:55:42.470183+00:00
-- url     : https://prove2.me/theorems/38e9892c-9fb5-4e5a-871a-265a316d3653
-- title:
--   Primorial bound $n\#\cdot25^n<68^n$ for $8\cdot10^6<n\le1.6\cdot10^7$
-- statement:
--   For every natural number $n$ with $8000000<n\le16000000$, the primorial $n\#=\prod_{p\le n,\ p\text{ prime}}p$ satisfies $n\#\cdot25^n<68^n$. Equivalently, $\theta(n)<n\log(68/25)$ on this range, where $\theta(n)=\sum_{p\le n}\log p$.
-- source:
--   Derived from Schoenfeld, Math. Comp. 30, 1976, 337-360, p. 356, display 5.1*; used in Liu and Wang, Acta Arith. 105, 2002, 133-175.

import Mathlib

namespace LL_Decomp368b
theorem primorial_c4 (n : ℕ) (hn : 8000000 < n) (hn' : n ≤ 16000000) :
    primorial n * 25 ^ n < 68 ^ n := by sorry
end LL_Decomp368b
