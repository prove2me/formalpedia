-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_monotoneNullMeasurableSetIntegralLeftLimit
-- name    : Kyprianou.Ch08.StageB.monotoneNullMeasurableSetIntegralLeftLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:45:48.363567+00:00
-- url     : https://prove2.me/theorems/23c0e5e8-b9b9-499a-9824-f3e0c6932d16
-- title:
--   Lemma 8.2 analytic extension: strict-left set-integral convergence from null-measurable events
-- statement:
--   For integrable real payoffs on a measure space, an increasing real-indexed family of events that is measurable up to null sets has left-continuous restricted integrals whenever almost every point with nonzero payoff in the height event already lies in some smaller-height event. The proof should use countably many rational thresholds, measurable representatives, and the already Proved monotoneSetIntegralLeftLimitFromAEMargin. This avoids assuming raw events are exactly measurable.
-- source:
--   Exact set-integral probability lemma for Kyprianou Chapter 8 Lemma 8.2, connected source measure-theory child ea08ebfa-d932-42e6-8306-2d4518ebe8e4. Existing Proved general measurable lemma 955f029e-888c-424d-948a-8ea81f15a334.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem Kyprianou.Ch08.StageB.monotoneNullMeasurableSetIntegralLeftLimit
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ) (A : ℝ → Set Ω)
    (hMeas : ∀ h : ℝ, NullMeasurableSet (A h) P)
    (hMono : Monotone A)
    (hInt : Integrable g P)
    (hMargin : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ A y →
        ∃ h : ℝ, h < y ∧ ω ∈ A h) :
    ∀ y : ℝ,
      Tendsto (fun h : ℝ => (∫ ω in A h, g ω ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in A y, g ω ∂P)) := by
  sorry
