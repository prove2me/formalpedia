-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_interval_mass_summable
-- name    : Kyprianou.Ch08.StageB.source_scale_discount_interval_mass_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:23:34.115657+00:00
-- url     : https://prove2.me/theorems/bb03ff84-a580-4c69-8595-89cb8abb3670
-- title:
--   Interval source scale convolution coefficient masses summable
-- statement:
--   Uniform factorial domination on finite reserve intervals gives absolute summability of all source scale convolution power integrals. Use existing source_scale_compact_factorial_majorant and Mathlib norm_integral_le_of_norm_le_const.
-- source:
--   Kyprianou (2006), Lemma 8.5

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB
theorem source_scale_discount_interval_mass_summable
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    Summable (fun n : ℕ =>
      ∫ y in (0 : ℝ)..x,
        q ^ n * scaleConvolutionPower (W 0) n y) := by
  sorry
end Kyprianou.Ch08.StageB
