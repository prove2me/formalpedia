-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_at_zero
-- name    : Kyprianou.Ch08.StageB.source_scale_discount_series_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:38:01.667385+00:00
-- url     : https://prove2.me/theorems/8001f01c-cd35-4501-b030-763864435103
-- title:
--   Source q-scale convolution series agreement at the origin
-- statement:
--   For every q≥0, the actual q-scale value W^(q)(0) equals the corresponding causal zero-discount power series at x=0. All higher convolution powers vanish at zero, so the essential source obligation is W^(q)(0)=W^(0)(0), independent of discount. This endpoint case is logically distinct from the Laplace-uniqueness result valid only on x>0, and is required by the exact all-nonnegative-reserves Lemma 8.3 (8.24).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3 (8.24) and Lemma 8.6 initial-value identity, pp.221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- The source discounted scale family agrees with the series at the origin. -/
theorem source_scale_discount_series_at_zero
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ((W q 0 : ℝ) : ℂ) =
      ∑' n : ℕ, (q : ℂ) ^ n *
        ((scaleConvolutionPower (W 0) n 0 : ℝ) : ℂ) := by
  sorry

end Kyprianou.Ch08.StageB
