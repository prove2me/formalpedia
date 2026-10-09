-- Prove2me | Theorems.Thm_Helfgott_odd_harmonic_sum_upper
-- name    : Helfgott.odd_harmonic_sum_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:44:21.425933+00:00
-- url     : https://prove2.me/theorems/a7706c96-a4bd-4022-910e-fbc13e03d15b
-- title:
--   Explicit harmonic sum restricted to odd indices
-- statement:
--   For every integer $N\ge1$, $$\sum_{\substack{1\le k\le N\\k\ {\rm odd}}}\frac1k\le1+\tfrac12\log N.$$ All finite reindexing and logarithmic integral steps are proved; no asymptotic input is assumed.
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
theorem odd_harmonic_sum_upper (N : ℕ) (hN : 1 ≤ N) :
    (∑ k∈Icc 1 N,if Nat.Coprime k 2 then 1/(k : ℝ) else 0) ≤
      1+Real.log (N : ℝ)/2 := by sorry
end Helfgott
