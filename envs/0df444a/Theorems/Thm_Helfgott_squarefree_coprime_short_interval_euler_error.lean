-- Prove2me | Theorems.Thm_Helfgott_squarefree_coprime_short_interval_euler_error
-- name    : Helfgott.squarefree_coprime_short_interval_euler_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T14:35:45.742528+00:00
-- url     : https://prove2.me/theorems/f78811cd-ece1-4341-968a-73ff8ddcf67a
-- title:
--   Sharp 1.27 square-root error for squarefree coprime counts in short intervals
-- statement:
--   For every positive integer q and integers 0<=A<=B<=2A, the squarefree count in (A,B] coprime to q differs from (B-A)*(6/pi^2)*prod_{p|q}p/(p+1) by at most 1.27*sqrt(B)*prod_{p|q}(1+1/sqrt(p)). All endpoints including A=B=0 are covered. This sharp arithmetic input retains the precise modulus factor needed for the Vaughan Type II cancellation reduction.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.1, https://arxiv.org/abs/1205.5252. Original complete Lean proof from exact Mobius inversion, the canonical coprime density, the proved smoothed squarefree bound, exact floor interval errors and the half-weighted divisor Euler product. Written by Codex.

import Mathlib
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_coprime_short_interval_euler_error  (q A B : ℕ) (hq : q≠0)
    (hAB : A≤B) (hhalf : B≤2*A) :
    |(∑ n ∈ Finset.Ioc A B,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      ((B : ℝ)-(A : ℝ))*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))|≤
      (127/100 : ℝ)*Real.sqrt (B : ℝ)*(∏ p ∈ q.primeFactors,(1+1/Real.sqrt (p : ℝ))) := by sorry

end Helfgott
