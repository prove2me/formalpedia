-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clockMeanLimit
-- name    : Kyprianou.Ch04.clockMeanLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:43:26.101563+00:00
-- url     : https://prove2.me/theorems/9096102f-b65c-4b9a-a44c-4c580ab2a16e
-- title:
--   Limit of bounded antitone means at exponential clocks
-- statement:
--   Apply the clock averaging bounds to each exponential clock pushforward. The early-clock error tends to zero, and the squeeze lemma gives convergence.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.clockMeanLimit
    (f : NNReal → ℝ) (hm : Measurable f) (ha : Antitone f)
    (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1)
    (ell : ℝ) (hlow : ∀ t, ell ≤ f t) (hlim : Tendsto f atTop (nhds ell))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (herr : ∀ T : NNReal, Tendsto (fun n => 1 - Real.exp (-(q n * (T : ℝ)))) atTop (nhds 0)) :
    Tendsto (fun n => ∫ t, f t ∂((expMeasure (q n)).map Real.toNNReal)) atTop (nhds ell) := by
  sorry
