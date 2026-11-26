-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45TaylorBoundV2
-- name    : Kyprianou.Ch04.exercise45TaylorBoundV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:09:58.690167+00:00
-- url     : https://prove2.me/theorems/b09db68a-ec88-462f-8010-4fa546eb740c
-- title:
--   exercise45TaylorBoundV2
-- statement:
--   exercise45TaylorBoundV2
-- source:
--   Exercise 4.5(iii), pure-jump Ito limit

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45TaylorBoundV2
    (f g h : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContDiff ℝ 2 f)
    (hg : ∀ x, g x = deriv f x) (hh : ∀ x, h x = deriv g x)
    (hF : ∀ x, |f x| ≤ K) (hG : ∀ x, |g x| ≤ K) (hH : ∀ x, |h x| ≤ K)
    (x z : ℝ) :
    |f (x+z)-f x-z*g x| ≤ (2*K+K*|z|) ∧
    |f (x+z)-f x-z*g x| ≤ K*z^2 := by
  sorry
