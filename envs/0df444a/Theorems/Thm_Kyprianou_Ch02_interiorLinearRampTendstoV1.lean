-- Prove2me | Theorems.Thm_Kyprianou_Ch02_interiorLinearRampTendstoV1
-- name    : Kyprianou.Ch02.interiorLinearRampTendstoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:11:25.848128+00:00
-- url     : https://prove2.me/theorems/065fda94-2d72-42f3-af91-0c8c3b055ed7
-- title:
--   Pointwise convergence of the interior linear ramps
-- statement:
--   Outside the interval the ramps vanish, while inside the first ramp tends to x and is eventually below the upper ramp.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.interiorLinearRampTendstoV1
    (r : ℝ) (hr : 0 < r) (x : ℝ) :
    Tendsto (fun n : ℕ => min (max 0 (x - 1 / ((n : ℝ) + 1))) (max 0 (((n : ℝ) + 1) * (r - x)))) atTop
      (nhds ((Ioo (0 : ℝ) r).indicator id x)) := by
  sorry
