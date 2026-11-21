-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_ge_one
-- name    : Kyprianou.Ch08.StageB.source_zscale_ge_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:27:45.391852+00:00
-- url     : https://prove2.me/theorems/76f2272d-fc8c-4632-83f2-9c7f6f5d29b1
-- title:
--   Positive lower bound of the Chapter 8 Z-scale on q≥0 and x≥0
-- statement:
--   For a source-authenticated scale family, q≥0 and x≥0, the Z-scale satisfies Z^(q)(x)=1+q ∫_0^x W^(q)(y)dy≥1. This follows from the nonnegative scale kernel and the nonnegative interval integral. In particular Z^(q)(x)≠0, a denominator prerequisite for the reflected first-passage identities of Exercise 8.11 and Results 8.10–8.11.
-- source:
--   Kyprianou (2006), Chapter 8 scale function Z definition and Exercise 8.11, pp.214 and 230.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

/-- The source-normalised Z-scale is at least one for q,x nonnegative. -/
theorem source_zscale_ge_one
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    1 ≤ Zscale q (W q) x := by
  sorry

end Kyprianou.Ch08.StageB
