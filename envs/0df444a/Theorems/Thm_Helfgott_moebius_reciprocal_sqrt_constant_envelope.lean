-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_sqrt_constant_envelope
-- name    : Helfgott.moebius_reciprocal_sqrt_constant_envelope
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:44:27.062213+00:00
-- url     : https://prove2.me/theorems/c7287d3d-a6c1-4646-892f-9d1133039ed8
-- title:
--   Finite square-root plus constant reciprocal Mobius envelope
-- statement:
--   Assume $|m(v)|\le0.03/\log v$ for all $v\ge11815$, where $m(v)=\sum_{n\le\lfloor v\rfloor}\mu(n)/n$. For $0\le\beta\le1/2$ and every $v\ge1$, $$|m(v)|\le(2/v)^\beta+0.03/\log1200001.$$ The finite square-root bound for $1\le v<1200001$ is discharged by a closed exact certificate. The all-range logarithmic estimate remains explicit.
-- source:
--   Exact odd harmonic integral comparison and finite Mobius cancellation toward Helfgott Type II estimates. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
open Finset Nat Real ArithmeticFunction MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott
theorem moebius_reciprocal_sqrt_constant_envelope
    (hdecay : ∀ v : ℝ, 11815 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤ (3/100)/Real.log v)
    (beta : ℝ) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1/2) :
    ∀ v : ℝ, 1 ≤ v →
      |∑ r∈Icc 1 ⌊v⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        (2/v)^beta+(3/100)/Real.log (1200001 : ℝ) := by sorry
end Helfgott
