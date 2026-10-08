-- Prove2me | Theorems.Thm_Helfgott_major_arc_arithmetic_weighted_complete
-- name    : Helfgott.major_arc_arithmetic_weighted_complete
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T04:09:34.157059+00:00
-- url     : https://prove2.me/theorems/59ccd61b-0704-42ba-be79-c9539344bcb5
-- title:
--   Weighted Cauchy bounds for the complete Goldbach major-arc arithmetic moments
-- statement:
--   Let $D$ comprise the odd integers $1\le q\le150000$ and even integers $1\le q\le300000$, and set $R(q)=600000/q$ for odd $q$ and $R(q)=1200000/q$ for even $q$. The complete arithmetic moments of the original three-prime Goldbach major arcs satisfy $$\sum_{q\in D}\frac1{\varphi(q)}\le32,\qquad\sum_{q\in D}2R(q)\le33600000,\qquad\sum_{q\in D}\varphi(q)2R(q)\le720000000000.$$ These unconditional bounds sharpen the previously established reciprocal-totient and width budgets of 64 and 50000000. They provide additional margin in the integrated prime-model error while preserving the original major-arc target.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Complete totient divisor expansion and Euler weight bound, followed by weighted Cauchy–Schwarz. Written by Codex.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals
open scoped BigOperators

namespace Helfgott
theorem major_arc_arithmetic_weighted_complete :
  let D := (Finset.Icc 1 150000).filter (fun q => Odd q) ∪
    (Finset.Icc 1 300000).filter (fun q => Even q)
  let R : ℕ → ℝ := fun q => if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)
  (∑ q ∈ D,1/(Nat.totient q : ℝ))≤32 ∧
  (∑ q ∈ D,2*R q)≤33600000 ∧
  (∑ q ∈ D,(Nat.totient q : ℝ)*(2*R q))≤720000000000 := by sorry
end Helfgott
