-- Prove2me | Theorems.Thm_Kyprianou_Ch02_measurableRightContinuousPathOfDenseGridV1
-- name    : Kyprianou.Ch02.measurableRightContinuousPathOfDenseGridV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:33:01.50218+00:00
-- url     : https://prove2.me/theorems/6f3199f7-e95a-41e6-8e51-af55704eabd6
-- title:
--   Measurable path map from measurable dense-grid observations and right continuity
-- statement:
--   Every sample path is right continuous, and its evaluations on a fixed dense countable time sequence are measurable. Prove the whole path map measurable into the product measurable space, using a sequence of grid points approaching each time from above and pointwise limits of measurable evaluations. No probability law or cadlag left limits are needed.
-- source:
--   Kyprianou (2006) Chapter 2 source-Levy regularity; LeanLevy imported Processes.StochasticProcess and Processes.LevyProcess

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.measurableRightContinuousPathOfDenseGridV1
    {Ω : Type} [MeasurableSpace Ω] (Y : Ω → ℝ≥0 → ℝ)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (hgrid : ∀ k : ℕ, Measurable (fun ω => Y ω (grid k)))
    (hRight : ∀ ω t, ContinuousWithinAt (Y ω) (Ici t) t) :
    Measurable Y := by
  sorry
