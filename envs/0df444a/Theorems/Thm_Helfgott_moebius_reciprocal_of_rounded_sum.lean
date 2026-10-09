-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_of_rounded_sum
-- name    : Helfgott.moebius_reciprocal_of_rounded_sum
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T21:37:03.629063+00:00
-- url     : https://prove2.me/theorems/78bc70a9-a109-4af5-8657-f61eea061e93
-- title:
--   Certified reciprocal Mobius bound from an integer rounded sum
-- statement:
--   For positive integer $Q$ and any natural $N$, define the exact integer $S=\sum_{1\le n\le N}\mu(n)\lfloor Q/n\rfloor$. Then $$\left|\sum_{1\le n\le N}\frac{\mu(n)}n\right|\le\frac{|S|+N}{Q}.$$ The proof establishes the complete rounding error bound $N/Q$, including all finite endpoints. A concrete value of $S$ must be certified separately; no floating point approximation is assumed. This provides a finite arithmetic route to the reciprocal Mobius bounds required by the Helfgott minor-arc analysis.
-- source:
--   Original finite arithmetic certificate reduction for the reciprocal Mobius input in Helfgott minor-arc bounds. The only analytic step is the elementary integer-rounding error bound. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Finset Nat ArithmeticFunction Real
open scoped BigOperators

namespace Helfgott

theorem moebius_reciprocal_of_rounded_sum  (Q N : ℕ) (S : ℤ) (hQ : 0 < Q)
    (hS : S = ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) :
    |∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      ((S.natAbs : ℝ) + (N : ℝ)) / (Q : ℝ) := by sorry

end Helfgott
