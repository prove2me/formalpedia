-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_path_weight_compact_bound
-- name    : Kyprianou.Ch04.ito43_path_weight_compact_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:15:16.906401+00:00
-- url     : https://prove2.me/theorems/d2cf1033-a82c-41d9-ad2c-d3ec3d0c03f4
-- title:
--   Continuous weights on a compact cadlag path and its left limits are bounded
-- statement:
--   Obtain a common compact state interval for the path and its positive-time left limits. The continuous weight is bounded on the compact time-state rectangle.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set

theorem Kyprianou.Ch04.ito43_path_weight_compact_bound {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ s ≤ T, |g ((s:ℝ),X s w)| ≤ M) ∧
      (∀ s : NNReal, 0 < s → s ≤ T → |g ((s:ℝ),L s w)| ≤ M) := by sorry
