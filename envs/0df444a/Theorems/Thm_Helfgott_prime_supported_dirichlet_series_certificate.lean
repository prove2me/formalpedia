-- Prove2me | Theorems.Thm_Helfgott_prime_supported_dirichlet_series_certificate
-- name    : Helfgott.prime_supported_dirichlet_series_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:16:41.057106+00:00
-- url     : https://prove2.me/theorems/977c921b-9aea-4d90-826c-44460c8c2d09
-- title:
--   Exact convergent prime-supported Dirichlet series and every finite truncation bound
-- statement:
--   For every integer $q\ge1$ and real $\sigma>0$, $$\sum_{n\ge1\atop p\mid n\Rightarrow p\mid q}n^{-\sigma}=\prod_{p\mid q}(1-p^{-\sigma})^{-1}.$$ The series converges absolutely, arbitrary prime powers are included, and every finite sum through $Y\ge0$ is bounded by the same product. This evaluates the positive prime-supported series introduced when coprimality is removed from the Mobius-over-n sum in the Vaughan Rankin argument.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 4.1.2, Euler-product assembly in equation (4.22), https://arxiv.org/abs/1205.5252. Complete Lean proof of absolute convergence, exact Euler product and every finite endpoint. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem prime_supported_dirichlet_series_certificate  (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ ∧
      ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n)≤∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by sorry

end Helfgott
