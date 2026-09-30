-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_linear_pieces_zero
-- name    : NHPPArrivals.LinearRate.linear_pieces_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:20:48.91485+00:00
-- url     : https://prove2.me/theorems/c7e8556b-ca2a-444b-a2c8-9839d7de8415
-- title:
--   LEMMA 1 (19) — Λ_j, F_j, p_j and r_j for a linear rate with a = 0
-- statement:
--   Let $\lambda(t) = bt$ on $[0,T]$ with $T > 0$ and $b > 0$. Divide $[0,T]$ into $k \ge 1$ subintervals of length $T/k$. For $1 \le j \le k$,
--
--   1. $\displaystyle \Lambda_j(t) = \frac{bt\big(kt + 2(j-1)T\big)}{2k}$ for $0 \le t \le T/k$;
--   2. $\displaystyle F_j(t) = \frac{t(2j - 2 + t)}{2j - 1}$ for $0 \le t \le 1$;
--   3. $\displaystyle p_j = \frac{2j-1}{k^2}$;
--
--   and for $2 \le j \le k$,
--
--   4. $\displaystyle r_j = \frac{k}{(j-1)T}$.
--
--   These closed forms make THEOREM 5's formula (22) explicit.
--
--   **Formalization Note** The paper prints the range of $r_j$ as $1 \le j \le k$, but $r_1 = b/\lambda(0) = b/0$ is undefined (the rate vanishes at the left end of the first subinterval), and (22) treats $j = 1$ separately; the statement asserts the formula for $r_j$ only for $2 \le j \le k$. $b > 0$ excludes the identically zero rate.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, p. 473, LEMMA 1, (19)

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

namespace NHPPArrivals.LinearRate

theorem linear_pieces_zero (b T : ℝ) (k : ℕ) (hT : 0 < T) (hb : 0 < b) (hk : 1 ≤ k) :
    (∀ j ∈ Finset.Icc 1 k, ∀ t ∈ Set.Icc (0:ℝ) (T / k),
      subCum (linRate 0 b) T k j t = b * t * ((k:ℝ) * t + 2 * ((j:ℝ) - 1) * T) / (2 * k)) ∧
    (∀ j ∈ Finset.Icc 1 k, ∀ t ∈ Set.Icc (0:ℝ) 1,
      subCdf (linRate 0 b) T k j t = t * (2 * (j:ℝ) - 2 + t) / (2 * (j:ℝ) - 1)) ∧
    (∀ j ∈ Finset.Icc 1 k, weight (linRate 0 b) T k j = (2 * (j:ℝ) - 1) / (k:ℝ) ^ 2) ∧
    (∀ j ∈ Finset.Icc 2 k, subSlope 0 b T k j = k / (((j:ℝ) - 1) * T)) := by sorry

end NHPPArrivals.LinearRate
