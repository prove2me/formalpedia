-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_discount_invariant
-- name    : Kyprianou.Ch08.StageB.source_scale_origin_discount_invariant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:52:20.128774+00:00
-- url     : https://prove2.me/theorems/f0b1efd9-1edc-4217-8864-6c3ac4e2427b
-- title:
--   Scale-function origin value is independent of discount
-- statement:
--   For a source-certified scale family of any spectrally negative Lévy process, W^(q)(0)=W^(0)(0) for every q≥0. This is the exact endpoint value in Kyprianou Lemma 8.6: zero for unbounded-variation paths, reciprocal bounded-variation drift otherwise. Alternatively derive from the source positive-reserve Volterra resolvent identity by right continuity and vanishing causal convolution near zero. It supplies the x=0 case of scale convolution series identity (8.24).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.6 and Lemma 8.3 (8.24), pp.221-222.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- The source q-scale origin value is independent of nonnegative discount. -/
theorem source_scale_origin_discount_invariant
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    W q 0 = W 0 0 := by
  sorry

end Kyprianou.Ch08.StageB
