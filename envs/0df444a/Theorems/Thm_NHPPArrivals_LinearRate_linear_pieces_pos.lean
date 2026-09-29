-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_linear_pieces_pos
-- name    : NHPPArrivals.LinearRate.linear_pieces_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:20:14.041757+00:00
-- url     : https://prove2.me/theorems/062f3f4f-c033-45f9-925d-c19bc0b14a2e
-- title:
--   LEMMA 1 (18) — Λ_j, F_j, p_j and r_j for a linear rate with a > 0
-- statement:
--   Let $\lambda(t) = a + bt$ on $[0,T]$ with $T > 0$, $a > 0$, $b \ge 0$, and $r = b/a$. Divide $[0,T]$ into $k \ge 1$ subintervals of length $T/k$ and let $1 \le j \le k$. Then
--
--   1. $\displaystyle \Lambda_j(t) = \frac{at\big(k(2 + rt) + 2(j-1)rT\big)}{2k}$ for $0 \le t \le T/k$;
--   2. $\displaystyle F_j(t) = \frac{t\big(2k + (2j - 2 + t)rT\big)}{2k + (2j-1)rT}$ for $0 \le t \le 1$;
--   3. $\displaystyle p_j = \frac{2k + (2j-1)rT}{k^2(2 + rT)}$;
--   4. $\displaystyle r_j = \frac{b}{\lambda((j-1)T/k)} = \frac{bk}{a\big(k + (j-1)rT\big)}$.
--
--   Here $\Lambda_j$, $F_j$, $p_j$ are the subinterval cumulative rate, conditional cdf and weight of LEMMA 1, (17), and $r_j$ is the relative slope of the rate on the $j$-th subinterval. These closed forms make THEOREM 5's formula (21) explicit.
--
--   **Formalization Note** $b \ge 0$ is §3.3's standing assumption. $\Lambda_j$, $F_j$, $p_j$ and $r_j$ are the general definitions of (17) and (18) applied to $\lambda(t) = a + bt$; the theorem asserts that they equal the closed forms.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, p. 472, LEMMA 1, (18)

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

namespace NHPPArrivals.LinearRate

theorem linear_pieces_pos (a b T : ℝ) (k : ℕ) (hT : 0 < T) (ha : 0 < a) (hb : 0 ≤ b)
    (hk : 1 ≤ k) (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
    (∀ t ∈ Set.Icc (0:ℝ) (T / k), subCum (linRate a b) T k j t =
      a * t * ((k:ℝ) * (2 + (b / a) * t) + 2 * ((j:ℝ) - 1) * (b / a) * T) / (2 * k)) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1, subCdf (linRate a b) T k j t =
      t * (2 * k + (2 * (j:ℝ) - 2 + t) * (b / a) * T) / (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T)) ∧
    weight (linRate a b) T k j =
      (2 * k + (2 * (j:ℝ) - 1) * (b / a) * T) / ((k:ℝ) ^ 2 * (2 + (b / a) * T)) ∧
    subSlope a b T k j = b * k / (a * (k + ((j:ℝ) - 1) * (b / a) * T)) := by sorry

end NHPPArrivals.LinearRate
