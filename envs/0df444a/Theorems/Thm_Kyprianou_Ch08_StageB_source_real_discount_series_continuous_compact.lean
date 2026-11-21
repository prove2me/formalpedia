-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_continuous_compact
-- name    : Kyprianou.Ch08.StageB.source_real_discount_series_continuous_compact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:23:39.376184+00:00
-- url     : https://prove2.me/theorems/7667b919-73c5-45ec-a755-72ba58ec6618
-- title:
--   Local uniform convergence and continuity of source scale series on a finite reserve interval
-- statement:
--   For any R>0 and q≥0, the source series Σ q^n Fn(x) is continuous on [0,R]. The factorial upper bound Fn(x)≤W0(R)(R W0(R))^n/n! uniformly for x∈[0,R] yields summability of the majorant and continuousOn_tsum.
-- source:
--   Kyprianou (2006) Chapter 8 Lemma 8.3 estimate (8.23), p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_real_discount_series_continuous_compact
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q R : ℝ)
    (hq : 0 ≤ q) (hR : 0 < R) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ,
      q ^ n * scaleConvolutionPower (W 0) n x)
      (Set.Icc (0 : ℝ) R) := by
  sorry
end Kyprianou.Ch08.StageB
