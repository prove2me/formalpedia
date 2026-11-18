-- Prove2me | Theorems.Thm_LL_Decomp551a_primorial_c5_lower_first
-- name    : LL_Decomp551a.primorial_c5_lower_first
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-17T15:39:39.703016+00:00
-- url     : https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0
-- title:
--   Primorial bound $n\#\cdot25^n<68^n$ for $1.6\cdot10^7<n\le2.0\cdot10^7$
-- statement:
--   For every natural number $n$ with $16000000<n\le20000000$, the primorial $n\#=\prod_{p\le n,\ p\text{ prime}}p$ satisfies $n\#\cdot25^n<68^n$. Equivalently, $\theta(n)<n\log(68/25)$ on this range, where $\theta(n)=\sum_{p\le n}\log p$.
-- source:
--   Derived from Schoenfeld, Math. Comp. 30, 1976, 337-360, p. 356, display 5.1*; used in Liu and Wang, Acta Arith. 105, 2002, 133-175.

import Mathlib

namespace LL_Decomp551a
theorem primorial_c5_lower_first (n : ℕ) (hn : 16000000 < n) (hn' : n ≤ 20000000) :
    primorial n * 25 ^ n < 68 ^ n := by sorry
end LL_Decomp551a
