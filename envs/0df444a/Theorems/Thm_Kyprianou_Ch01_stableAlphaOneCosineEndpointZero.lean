-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineEndpointZero
-- name    : Kyprianou.Ch01.stableAlphaOneCosineEndpointZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:01:34.274557+00:00
-- url     : https://prove2.me/theorems/e830333d-c10f-4741-b2b4-c04e6515a968
-- title:
--   Near-zero vanishing of the index-one cosine integration-by-parts boundary term
-- statement:
--   As r tends to zero from the right, (1−cos r)/r tends to zero. This is the exact lower-boundary term needed to integrate the stable alpha-one cosine kernel by parts and reduce the numerical integral to a Dirichlet sine integral. The statement follows from differentiability at zero with derivative zero.
-- source:
--   Kyprianou (2006), Chapter 1, stable alpha-one cosine integral.

import Mathlib
open MeasureTheory Filter Set Real
set_option autoImplicit false
open scoped Topology

theorem Kyprianou.Ch01.stableAlphaOneCosineEndpointZero :
    Tendsto (fun r : ℝ => (1 - Real.cos r) / r)
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry
