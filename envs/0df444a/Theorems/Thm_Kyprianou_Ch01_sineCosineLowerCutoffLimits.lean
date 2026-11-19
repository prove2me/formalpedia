-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sineCosineLowerCutoffLimits
-- name    : Kyprianou.Ch01.sineCosineLowerCutoffLimits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:15:19.508537+00:00
-- url     : https://prove2.me/theorems/a45a590d-0cec-4c71-b4e7-53ea4ccd4136
-- title:
--   Positive-lower-cutoff convergence for sine and cosine kernels
-- statement:
--   For a fixed positive upper horizon, as the strictly positive lower integration limit decreases to zero, the sine quotient and cosine kernel interval integrals converge to the corresponding zero-endpoint integrals. The sine quotient has a removable almost-everywhere singularity via the continuous sinc function; the cosine kernel is absolutely integrable by the already-Proved stable index-one theorem.
-- source:
--   Kyprianou (2006), Chapter 1 Dirichlet sine integral; source-proven stableAlphaOneCosineFiniteIntegrationByParts and stableAlphaOneCosineEndpointZero.

import Mathlib
open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.sineCosineLowerCutoffLimits
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun a : ℝ => ∫ x in a..R, Real.sin x / x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in (0 : ℝ)..R, Real.sin x / x)) ∧
    Tendsto (fun a : ℝ => ∫ x in a..R, (1 - Real.cos x) / x ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in Set.Ioc (0 : ℝ) R,
        (1 - Real.cos x) / x ^ 2 ∂volume)) := by
  sorry
