-- Prove2me | Theorems.Thm_OddGoldbach19_large_count_exp260
-- name    : OddGoldbach19.large_count_exp260
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T18:17:32.746197+00:00
-- url     : https://prove2.me/theorems/d0641bda-022b-49b2-803c-a9ec60af7910
-- title:
--   Odd-prime sum counting beyond exp260
-- statement:
--   Let $r(s)$ count representations of $s$ by two odd primes, using the shared campaign definitions, and write $R(n)=\#\{0\le s\le n:r(s)>0\}$. For every natural number $n\ge e^{260}$,
--   $$R(n)\ge\frac{100}{1799}\,n.$$
--   This lowers the large-range threshold of the previously proved estimate from $e^{410}$ to $e^{260}$. It is a supporting counting estimate, not a complete19-prime campaign endpoint.
-- source:
--   New explicit refinement of the existing Riesel-Vaughan interval-weighted argument, using the proved coefficient-five interval Goldbach estimate, proved .46 second-order prime counting, and shifted-square concavity. The cutoff260 is derived by the attached exact polynomial and tail comparisons, not quoted from the source paper. Context: Riesel and Vaughan, On sums of primes (1983).

import Mathlib
import Definitions.Def_Schnir_defs

theorem OddGoldbach19.large_count_exp260 (n : ℕ) (hn : Real.exp 260 ≤ (n : ℝ)) :
    (n : ℝ) * (100 / 1799) ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := by sorry
