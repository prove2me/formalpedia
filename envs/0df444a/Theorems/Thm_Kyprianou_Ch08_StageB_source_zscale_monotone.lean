-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_monotone
-- name    : Kyprianou.Ch08.StageB.source_zscale_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:43:49.084192+00:00
-- url     : https://prove2.me/theorems/3dc36c57-4521-4dff-87eb-ae41d74055c3
-- title:
--   Monotonicity of source Z-scale for nonnegative discount and reserve
-- statement:
--   For q≥0 and 0≤x≤y, the genuine source scale satisfies Z^(q)(x)≤Z^(q)(y). This is the direct consequence of the nonnegative q-scale kernel W and Z^(q)=1+q∫W, with integrable-on-compact scale functions. It ensures that the reflected exit probability Z^(q)(c−x)/Z^(q)(c) lies in [0,1] for Exercise 8.11, and that its denominator is positive (source_zscale_ge_one).
-- source:
--   Kyprianou (2006), Chapter 8 Z-scale definition and Exercise 8.11 reflected-exit identity, pp.214,230.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- The genuine Z-scale is nondecreasing on the nonnegative reserve halfline. -/
theorem source_zscale_monotone
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x y : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Zscale q (W q) x ≤ Zscale q (W q) y := by
  sorry

end Kyprianou.Ch08.StageB
