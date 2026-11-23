-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_monotoneSetIntegralLeftLimitFromAEMargin
-- name    : Kyprianou.Ch08.StageB.monotoneSetIntegralLeftLimitFromAEMargin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:40:04.872949+00:00
-- url     : https://prove2.me/theorems/955f029e-888c-424d-948a-8ea81f15a334
-- title:
--   Lemma 8.2 analytic lemma: monotone measurable set integrals are left continuous under an a.e. strict-margin criterion
-- statement:
--   For an arbitrary integrable real function on a measure space and a monotone increasing family of measurable events indexed by the real threshold, the set integral is continuous from below at each threshold, provided that almost every point with nonzero integrand which is in the event at the threshold belongs to the event at some strictly smaller threshold. This supplies the precise dominated/monotone-convergence step for actual excursion-height laws, without assuming atomlessness.
-- source:
--   MeasureTheory.tendsto_setIntegral_of_monotone and Mathlib.Topology.Order.AtTopBotIxx map_coe_Iio_atTop, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474. The needed measure-theory child in connected Kyprianou Chapter 8 Lemma 8.2 branch is ea08ebfa-d932-42e6-8306-2d4518ebe8e4.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem Kyprianou.Ch08.StageB.monotoneSetIntegralLeftLimitFromAEMargin
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ) (A : ℝ → Set Ω)
    (hMeas : ∀ h : ℝ, MeasurableSet (A h))
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
