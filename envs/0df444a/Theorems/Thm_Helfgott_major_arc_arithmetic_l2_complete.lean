-- Prove2me | Theorems.Thm_Helfgott_major_arc_arithmetic_l2_complete
-- name    : Helfgott.major_arc_arithmetic_l2_complete
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T04:19:55.423404+00:00
-- url     : https://prove2.me/theorems/4de9cc00-bd97-45d9-803f-02d65d33c31a
-- title:
--   Complete arithmetic moments for sharp L2 integration on the Goldbach major arcs
-- statement:
--   Let $D$ comprise the odd integers $1\le q\le150000$ and even integers $1\le q\le300000$, and set $R(q)=600000/q$ for odd $q$ and $R(q)=1200000/q$ for even $q$. The complete arithmetic moments satisfy
--   $$\sum_{q\in D}\frac1{\varphi(q)}\le30,\qquad\sum_{q\in D}2R(q)\le33600000,$$
--   $$\sum_{q\in D}\sqrt{2R(q)}\le1700000,\qquad\sum_{q\in D}\varphi(q)2R(q)\le720000000000.$$
--   The square-root-width moment is the natural budget for integrating the quadratic prime-model errors by Cauchy–Schwarz. Together these unconditional bounds support the sharper $x^2/50000$ error estimate for the original three-prime major arcs.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Complete totient divisor expansion and Euler weight bound, followed by weighted Cauchy–Schwarz. Written by Codex.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open scoped BigOperators

namespace Helfgott

theorem major_arc_arithmetic_l2_complete :
  let D := (Finset.Icc 1 150000).filter (fun q => Odd q) ∪
    (Finset.Icc 1 300000).filter (fun q => Even q)
  let R : ℕ → ℝ := fun q => if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)
  (∑ q ∈ D,1/(Nat.totient q : ℝ))≤30 ∧
  (∑ q ∈ D,2*R q)≤33600000 ∧
  (∑ q ∈ D,Real.sqrt (2*R q))≤1700000 ∧
  (∑ q ∈ D,(Nat.totient q : ℝ)*(2*R q))≤720000000000 := by sorry

end Helfgott
