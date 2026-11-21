-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_positive_x
-- name    : Kyprianou.Ch08.StageB.source_scale_discount_series_positive_x
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:38:02.450799+00:00
-- url     : https://prove2.me/theorems/0fb2c7c4-e6e0-419c-8684-ba0ed7d3d8a8
-- title:
--   Real-to-complex q-scale convolution series identification for x>0
-- statement:
--   The source positive-reserve q-scale function equals the complex causal convolution series for all q≥0 and x>0. This is the x>0 part of textbook identity (8.24) and can be proved using the Proved Laplace transform of each convolution power, positive geometric denominator above Φψ(q), integrability of the series and Proved Laplace uniqueness for nonnegative continuous functions. The root origin x=0 is handled separately.
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3 equation (8.24), printed p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- Identification of source q-scales with causal convolution series at positive x. -/
theorem source_scale_discount_series_positive_x
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    ((W q x : ℝ) : ℂ) =
      ∑' n : ℕ, (q : ℂ) ^ n *
        ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ) := by
  sorry

end Kyprianou.Ch08.StageB
