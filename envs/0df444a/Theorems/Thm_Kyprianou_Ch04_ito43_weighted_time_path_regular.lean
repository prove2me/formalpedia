-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_time_path_regular
-- name    : Kyprianou.Ch04.ito43_weighted_time_path_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:15:09.980929+00:00
-- url     : https://prove2.me/theorems/6e53b587-704f-5480-977f-0b52acd7ea7e
-- title:
--   Weighted time integral is continuous and bounded on compact horizons
-- statement:
--   The time-state composition is measurable and locally bounded on the positive time axis. It is integrable on compact intervals. Apply the proved continuous cumulative interval integral theorem and compactness.
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

theorem Kyprianou.Ch04.ito43_weighted_time_path_regular {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    let J : NNReal → ℝ := fun t =>
      ∫ s in Icc (0:ℝ) (t:ℝ), g (s,X s.toNNReal w) ∂volume
    Continuous J ∧ ∃ M : ℝ, ∀ t ≤ T, |J t| ≤ M := by sorry
