-- Prove2me | Theorems.Thm_Helfgott_squarefree_coprime_real_short_interval_euler_error
-- name    : Helfgott.squarefree_coprime_real_short_interval_euler_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T14:51:56.69299+00:00
-- url     : https://prove2.me/theorems/b4e5b4b6-e922-4b8d-926d-c386ad0d6492
-- title:
--   Sharp squarefree coprime short-interval error for real endpoints
-- statement:
--   For every positive integer q and real endpoints 0<=A<=B<=2A, the squarefree count in (A,B] coprime to q differs from (B-A)*(6/pi^2)*prod_{p|q}p/(p+1) by at most 1.27*sqrt(B)*prod_{p|q}(1+1/sqrt(p)). The count is over integers floor(A)<n<=floor(B); all endpoints including A=B=0 are covered. This sharp arithmetic input retains the precise modulus factor needed for the Vaughan Type II cancellation reduction.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1, https://arxiv.org/abs/1205.5252. Original complete Lean proof from exact Mobius inversion, the canonical coprime density, the proved smoothed squarefree bound, exact floor interval errors and the half-weighted divisor Euler product. Written by Codex.

import Mathlib
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_coprime_real_short_interval_euler_error  (q : ℕ) (A B : ℝ) (hq : q≠0)
    (hA : 0≤A) (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (B-A)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt B*(∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ))) := by sorry

end Helfgott
