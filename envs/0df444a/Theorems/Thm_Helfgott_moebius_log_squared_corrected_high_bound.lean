-- Prove2me | Theorems.Thm_Helfgott_moebius_log_squared_corrected_high_bound
-- name    : Helfgott.moebius_log_squared_corrected_high_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:27:01.358376+00:00
-- url     : https://prove2.me/theorems/95399120-a550-4e8e-83ac-d8b64f3dff65
-- title:
--   Corrected high-range log-squared Mobius estimate
-- statement:
--   For every natural $N\ge10^{26}$, suppose $|C|\le2$. Let $a_C(k)=(\Lambda*\Lambda)(k)-\Lambda(k)\log k+C$ and $A_C(u)=\sum_{k\le u}a_C(k)$. Assume $|A_C(\lfloor N/d\rfloor)|\le0.0065N/d$ for $d\le\lfloor N/10^{16}\rfloor$, and $\le0.031N/d$ for the remaining $d\le\lfloor N/(21\cdot10^9)\rfloor$. Assume $|M(u)|\le u/4345$ for every integer $u\ge2160535$, and the finite convolution moment $\sum_{k\le21\cdot10^9}|a_C(k)|/k+|A_C(21\cdot10^9)|/(21\cdot10^9)\le4345/4$. Then $|\sum_{n\le N}\mu(n)\log^2n|\le N(0.014\log N-0.23)$. All prime-error, coarse summatory, and finite moment inputs are explicit hypotheses.
-- source:
--   Independent standard-kernel corrected Mobius conversion, related to O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Written by Codex.

import Theorems.Thm_Helfgott_moebius_log_squared_two_range_hyperbola_bound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_log_squared_corrected_high_bound  (N : ℕ) (C : ℝ)
    (hN : 100000000000000000000000000 ≤ N) (hC : |C| ≤ 2)
    (hRhigh : ∀ d ∈ Icc 1 (N / 10000000000000000),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * ((N : ℝ) / (d : ℝ)))
    (hRmiddle : ∀ d ∈ Ioc (N / 10000000000000000) (N / 21000000000),
      |∑ k ∈ Icc 1 (N / d),
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * ((N : ℝ) / (d : ℝ)))
    (hM : ∀ u : ℕ, 2160535 ≤ u →
      |∑ d ∈ Icc 1 u, ((moebius d : ℤ) : ℝ)| ≤ (u : ℝ) / 4345)
    (hfinite :
      ((∑ k ∈ Icc 1 21000000000,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 21000000000,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (21000000000 : ℝ)) ≤ 4345 / 4) :
    |∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) ^ 2| ≤
      (N : ℝ) * ((7 / 500) * Real.log (N : ℝ) - 23 / 100) := by sorry

end Helfgott
