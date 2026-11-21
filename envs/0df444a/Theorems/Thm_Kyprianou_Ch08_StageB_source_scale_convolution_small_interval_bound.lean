-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_small_interval_bound
-- name    : Kyprianou.Ch08.StageB.source_scale_convolution_small_interval_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:56:11.118457+00:00
-- url     : https://prove2.me/theorems/7cbab157-b473-4f8d-a988-1090d77642e9
-- title:
--   Uniform endpoint upper bound for source q-scale causal convolution
-- statement:
--   For source scale functions W0 and Wq, q,x≥0, and integrability of their product over 0<s≤x, the causal convolution lies between zero and x W0(x)Wq(x). Both scale functions are nonnegative and nondecreasing, so each integrand is bounded by the endpoint product. This estimate plus scale continuity proves the convolution vanishes as reserve tends to 0, needed to show discount-independent W^(q)(0) and close the origin of Kyprianou (8.24).
-- source:
--   Kyprianou (2006), Chapter 8 Lemma 8.3 (8.23), p.221.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- Pointwise causal scale convolution bound by interval length times endpoint scales. -/
theorem source_scale_convolution_small_interval_bound
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x)
    (hi : IntegrableOn (fun s : ℝ => W 0 s * W q (x - s))
      (Set.Ioc (0 : ℝ) x) volume) :
    0 ≤ (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ∧
    (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) ≤
      x * W 0 x * W q x := by
  sorry

end Kyprianou.Ch08.StageB
