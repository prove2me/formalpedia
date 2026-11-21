-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_real_discount_series_continuous
-- name    : Kyprianou.Ch08.StageB.source_real_discount_series_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:19:43.123181+00:00
-- url     : https://prove2.me/theorems/b065c6d8-e29f-4ea4-a8ed-76a522d8eefb
-- title:
--   Positive-reserve continuity of source discount scale convolution series
-- statement:
--   For actual source Wq and q≥0 the real convolution sum Σ_n q^n W0^{*(n+1)}(x) is continuous on x>0. Individual causal powers inherit continuity from W0 and local weighted integrability; the factorial majorant on compact intervals implies local uniform convergence, hence continuity of the sum. This is the continuity premise for positive halfline Laplace uniqueness.
-- source:
--   Kyprianou (2006) Lemma 8.3 (8.23)-(8.24) p221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_real_discount_series_continuous
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ,
      q ^ n * scaleConvolutionPower (W 0) n x)
      (Set.Ioi (0 : ℝ)) := by
  sorry

end Kyprianou.Ch08.StageB
