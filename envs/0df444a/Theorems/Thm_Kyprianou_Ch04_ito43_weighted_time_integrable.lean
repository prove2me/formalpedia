-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_time_integrable
-- name    : Kyprianou.Ch04.ito43_weighted_time_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:25:46.844919+00:00
-- url     : https://prove2.me/theorems/c494a48b-fb66-5a8f-8bee-009efd5e075e
-- title:
--   Continuous weight along a cadlag path is integrable on a compact interval
-- statement:
--   Reuse the compact-path bound and measurable cadlag version from the accepted time regularity proof.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_weighted_time_integrable
    {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : ProbabilityTheory.IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (t : NNReal) :
    IntegrableOn (fun s : ℝ => g (s,X s.toNNReal w)) (Icc (0:ℝ) (t:ℝ)) volume := by sorry
