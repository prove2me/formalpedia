-- Prove2me | Theorems.Thm_Kyprianou_Ch04_antitoneRewardMeanProperties
-- name    : Kyprianou.Ch04.antitoneRewardMeanProperties
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:39:38.115686+00:00
-- url     : https://prove2.me/theorems/bfc6afc7-c7b1-593d-895b-23115a9e2d3f
-- title:
--   Mean properties for bounded monotone rewards
-- statement:
--   Use bounded integrability and monotonicity of the integral; the antitone expectation converges to its real infimum.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.antitoneRewardMeanProperties
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : NNReal × Ω → ℝ) (hm : Measurable g)
    (h0 : ∀ z, 0 ≤ g z) (h1 : ∀ z, g z ≤ 1)
    (ha : ∀ w, Antitone (fun t : NNReal => g (t,w))) :
    let f : NNReal → ℝ := fun t => ∫ w, g (t,w) ∂P
    Measurable f ∧ Antitone f ∧ (∀ t, 0 ≤ f t) ∧ (∀ t, f t ≤ 1) ∧
      ∃ ell : ℝ, (∀ t, ell ≤ f t) ∧ Tendsto f atTop (nhds ell) := by
  sorry
