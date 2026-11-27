-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_series_summable
-- name    : Kyprianou.Ch04.ito43_weighted_series_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:01:21.195117+00:00
-- url     : https://prove2.me/theorems/6ed23b71-8e1e-498d-94af-85f6e01fce67
-- title:
--   Compact weighted square-jump series is absolutely summable
-- statement:
--   A compact path weight is bounded, so squared jump summability dominates the weighted series.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch04
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_weighted_series_summable
    {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (t : NNReal) (hs : Summable (fun s : Ioc (0 : NNReal) t => (X s w-L s w)^2)) :
    Summable (fun s : Ioc (0 : NNReal) t =>
      |g (((s : NNReal) : ℝ), L s w) * (X s w-L s w)^2/2|) := by sorry
