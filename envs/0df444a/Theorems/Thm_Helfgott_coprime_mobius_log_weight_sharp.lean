-- Prove2me | Theorems.Thm_Helfgott_coprime_mobius_log_weight_sharp
-- name    : Helfgott.coprime_mobius_log_weight_sharp
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T21:31:56.523585+00:00
-- url     : https://prove2.me/theorems/d770779f-5389-4f2d-a662-26c0aa517033
-- title:
--   Uniform logarithmic moment bound for coprime Mobius sums
-- statement:
--   For integers $q,N\ge1$ and a real number $Y\ge N$,
--   $$\left|\sum_{\substack{1\le d\le N\\(d,q)=1}}\frac{\mu(d)}d\log\frac Yd\right|\le\log\frac YN+\frac q{\varphi(q)}+\frac83.$$
--   In particular, at $Y=N$ the bound is independent of $N$. This unconditional estimate retains Mobius cancellation in logarithmically weighted Type I sums.
-- source:
--   Elementary harmonic-number convolution and finite Euler product argument, formalized for the Prove2Me Weak Goldbach mission.

import Mathlib
open Finset ArithmeticFunction
open scoped BigOperators

theorem Helfgott.coprime_mobius_log_weight_sharp (q N : ℕ) (hq : 0 < q) (hN : 1 ≤ N)
    (Y : ℝ) (hY : (N:ℝ) ≤ Y) :
    |∑ d ∈ Icc 1 N, (if Nat.Coprime d q then ((moebius d:ℤ):ℝ)/(d:ℝ) else 0)*
      Real.log (Y/(d:ℝ))| ≤ Real.log (Y/(N:ℝ))+(q:ℝ)/(q.totient:ℝ)+8/3 := by sorry
