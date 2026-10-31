-- Prove2me | Theorems.Thm_OddGoldbach19_medium_count_log100
-- name    : OddGoldbach19.medium_count_log100
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:37:02.972066+00:00
-- url     : https://prove2.me/theorems/d6cfc72d-937e-401d-a0c2-22714f9ed672
-- title:
--   A strengthened prime-sum count for logarithms between26 and100
-- statement:
--   For $n\in\mathbb N$, let $R(n)$ count the integers $s\le n$ that are sums of two odd primes. If $26\le\log n\le100$, then
--   $$R(n)\ge\frac{100}{1799}n.$$
--   The estimate provides part of the uniform count needed for a Schnirelmann-density argument. It uses the known1000-prime finite-shift certificate together with explicit prime-pair estimates and a tighter upper bound for the twin-prime constant.
-- source:
--   Finite-shift second moment method of Riesel and Vaughan, On sums of primes (1983). The finite combinatorial identities are generalized from public Apache2.0 accepted Prove2Me proof2e6ffca0-db78-43ae-93a9-bc1793b1bf07 and related campaign proofs; the explicit interval and endpoint arithmetic here use the accepted private supporting estimates.

import Mathlib
import Definitions.Def_Schnir_defs

theorem OddGoldbach19.medium_count_log100 (n : ℕ)
    (hln : 26≤Real.log (n:ℝ)) (hlu : Real.log (n:ℝ)≤100) :
    (n:ℝ)*(100/1799:ℝ)≤(((Finset.range (n+1)).filter (fun s=>0<Schnir.r s)).card:ℝ) := by sorry
