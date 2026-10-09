-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_log_decay_of_integer_certificate
-- name    : Helfgott.moebius_reciprocal_log_decay_of_integer_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T21:50:45.831987+00:00
-- url     : https://prove2.me/theorems/d03f655b-7bb9-4949-9fb8-0372f6421880
-- title:
--   Real reciprocal Mobius logarithmic decay from finite integer certificates
-- statement:
--   Let $Q>0,N\ge2,L\ge0$ be integers, and let $S=\sum_{1\le n\le N}\mu(n)\lfloor Q/n\rfloor$. If $\log(N+1)\le L/10$ and $10(|S|+N)L\le3Q$, then every real $x$ with $N\le x<N+1$ satisfies $$\left|\sum_{1\le n\le\lfloor x\rfloor}\frac{\mu(n)}n\right|\le\frac{0.03}{\log x}.$$ This transfers exact integer rounded-sum checks and logarithm cutoffs to the real-variable reciprocal Mobius input in the Helfgott minor-arc argument.
-- source:
--   Original finite integer-certificate reduction toward the reciprocal Mobius bounds required by Helfgott minor arcs. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
open Finset Nat ArithmeticFunction Real
open scoped BigOperators

namespace Helfgott

theorem moebius_reciprocal_log_decay_of_integer_certificate 
    (Q N L : ℕ) (S : ℤ) (x : ℝ)
    (hQ : 0 < Q) (hN : 2 ≤ N) (hx : (N : ℝ) ≤ x) (hxnext : x < N + 1)
    (hS : S = ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ))
    (hlog : Real.log ((N + 1 : ℕ) : ℝ) ≤ (L : ℝ) / 10)
    (hnum : 10 * (S.natAbs + N) * L ≤ 3 * Q) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      (3 / 100 : ℝ) / Real.log x := by sorry

end Helfgott
