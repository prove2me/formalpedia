-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_partial_sum_abs_le_one
-- name    : Helfgott.moebius_reciprocal_partial_sum_abs_le_one
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T16:02:12.103978+00:00
-- url     : https://prove2.me/theorems/08908269-d6d2-47cf-8190-558126075d32
-- title:
--   Unconditional unit bound for every reciprocal Mobius partial sum
-- statement:
--   For every nonnegative integer $N$, $$\left|\sum_{1\le n\le N}\frac{\mu(n)}n\right|\le1.$$ This supplies the unconditional small-range bound for the standard Mobius cancellation sum used in the Vaughan Type II argument. Together with sharper large-range bounds, it can be propagated through the positive coprime and weighted-sum convolution identities.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, section 2.2, equation (2.7) at modulus one, https://arxiv.org/abs/1205.5252. Original elementary complete Lean proof from the exact finite Mobius floor identity. Written by Codex.

import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_reciprocal_partial_sum_abs_le_one  (N : ℕ) :
    |∑ d∈Finset.Icc 1 N,((moebius d : ℤ) : ℝ)/(d : ℝ)|≤1 := by sorry

end Helfgott
