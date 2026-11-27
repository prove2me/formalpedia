-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_real_path_right
-- name    : Kyprianou.Ch04.ito43_weighted_real_path_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:17:20.307489+00:00
-- url     : https://prove2.me/theorems/8e8f6ee4-80e8-59a1-9602-6713a1b8bbe7
-- title:
--   Weighted real-time path is right-continuous
-- statement:
--   Compose the right-sided path limit with the continuous weight, using nonnegative real time.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_weighted_real_path_right
    {Ω : Type} [MeasurableSpace Ω] (X : NNReal → Ω → ℝ) (w : Ω)
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (hc : ProbabilityTheory.IsCadlag (fun s => X s w))
    (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun r : ℝ => g (r, X r.toNNReal w)) (Ici t) t := by sorry
