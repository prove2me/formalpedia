-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineEndpointInfinity
-- name    : Kyprianou.Ch01.stableAlphaOneCosineEndpointInfinity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:05:52.392232+00:00
-- url     : https://prove2.me/theorems/30f9297c-3042-4460-80d5-f998b39281a6
-- title:
--   Vanishing at infinity of the index-one stable cosine integration-by-parts boundary term
-- statement:
--   As r tends to positive infinity, (1−cos r)/r tends to zero. The numerator is nonnegative and bounded above by two; the comparison 0≤(1−cos r)/r≤2/r and the inverse limit establish the endpoint needed for the improper cosine integral integration by parts.
-- source:
--   Kyprianou (2006), Chapter 1, stable alpha-one cosine integral.

import Mathlib
open MeasureTheory Filter Set Real
set_option autoImplicit false
open scoped Topology

theorem Kyprianou.Ch01.stableAlphaOneCosineEndpointInfinity :
    Tendsto (fun r : ℝ => (1 - Real.cos r) / r)
    atTop (𝓝 (0 : ℝ)) := by
  sorry
