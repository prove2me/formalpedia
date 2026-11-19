-- Prove2me | Theorems.Thm_Kyprianou_Ch01_continuousUpperPassageDiscountedExpLimitPublic
-- name    : Kyprianou.Ch01.continuousUpperPassageDiscountedExpLimitPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:13:23.862589+00:00
-- url     : https://prove2.me/theorems/3ffcc03e-cbef-4efe-ace4-03a60269d989
-- title:
--   Continuous path first-upper-passage stopped discounted exponential tends to boundary payoff
-- statement:
--   For a continuous path starting at zero, positive upper barrier, nonnegative adjustment exponent and positive discount, the exponentially discounted path stopped at the first strict upper passage or at horizon N converges to the barrier-weighted passage Laplace payoff as N grows. On finite first passage this is eventually constant by first contact; on infinite first passage the positive discount and no-crossing bound force exponential decay.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.10(ii), back-of-book solution, printed page 306. Stopping-time boundary limit.

import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01 Filter
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.continuousUpperPassageDiscountedExpLimitPublic
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (x theta q : ℝ) (hx : 0 < x) (hθ : 0 ≤ theta) (hq : 0 < q)
    (hcont : Continuous (fun t : ℝ≥0 => X t ω))
    (hzero : X 0 ω = 0) :
    Tendsto (fun N : ℕ =>
      let T : ℝ≥0 := N
      let tauT : ℝ≥0 :=
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Real.exp (theta * X tauT ω - q * (tauT : ℝ)))
      atTop (nhds (Real.exp (theta * x) *
        passageLaplace (firstUpperPassage X x) q ω)) := by sorry
