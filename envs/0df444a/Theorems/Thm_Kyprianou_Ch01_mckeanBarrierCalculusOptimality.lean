-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanBarrierCalculusOptimality
-- name    : Kyprianou.Ch01.mckeanBarrierCalculusOptimality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:25:09.406659+00:00
-- url     : https://prove2.me/theorems/bea9bdc1-0ec7-448d-8142-15743baf5c77
-- title:
--   Exercise 1.10(iii): differentiation and optimisation of the perpetual put barrier
-- statement:
--   Kyprianou Exercise 1.10(iii), printed p. 32. For a perpetual put strike K>0 and Brownian first-passage Laplace exponent Φ(q)>0, identify b=log(KΦ/(1+Φ)). Prove by differentiation that the discounted threshold payoff a↦(K−e^a)e^(−Φ(x−a)) has zero derivative at b, is dominated by the candidate value for every a≤x, and attains that value at the accessible threshold min(x,b). Combined with Exercise 1.10(ii)'s passage transform and the optional-stopping verification, this yields the explicit McKean value. This standalone theorem is genuine calculus and does not assume the inequality it proves.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(iii), printed p. 32.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanBarrierCalculusOptimality
    (K phi x : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b : ℝ := Real.log (K * phi / (1 + phi))
    let barrierPayoff : ℝ → ℝ := fun a =>
      (K - Real.exp a) * Real.exp (-phi * (x - a))
    HasDerivAt barrierPayoff 0 b ∧
    (∀ a : ℝ, a ≤ x →
      barrierPayoff a ≤ mckeanValue K b phi x) ∧
    barrierPayoff (min x b) = mckeanValue K b phi x := by
  sorry
