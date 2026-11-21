-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real
-- name    : Kyprianou.Ch08.StageB.source_scale_power_nonnegative_all_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:14:15.749574+00:00
-- url     : https://prove2.me/theorems/a9bd9b57-617d-445d-a101-4f3daa5220e2
-- title:
--   Every source scale convolution power is nonnegative globally
-- statement:
--   The zero-discount source q-scale kernel is nonnegative at every real argument, and its recursively defined positive-axis causal convolution powers remain nonnegative at every real argument. Induct through the causal Ioc integral using nonnegative product integrands. Supports positive series and monotone integration for Lemma 8.3.
-- source:
--   Kyprianou (2006) Lemma 8.3, (8.23)-(8.24), p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_scale_power_nonnegative_all_real
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    ∀ (n : ℕ) (x : ℝ),
      0 ≤ scaleConvolutionPower (W 0) n x := by
  sorry

end Kyprianou.Ch08.StageB
