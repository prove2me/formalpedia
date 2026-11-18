-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneRationalLintegralToReal
-- name    : Kyprianou.Ch01.stableAlphaOneRationalLintegralToReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:36:07.363437+00:00
-- url     : https://prove2.me/theorems/4b43baf8-6576-49e1-bb09-08d816b1f098
-- title:
--   Extended-to-real conversion for rational integral
-- statement:
--   The positive rational kernel 1/(1+a²) is nonnegative and absolutely integrable over the positive half-line. The pinned ofReal_integral_eq_lintegral_ofReal converts its Bochner integral to its extended nonnegative integral, and ENNReal.toReal_ofReal removes the conversion because the integral is nonnegative.
-- source:
--   Kyprianou (2006), Chapter 1, stable α=1 cosine integral and exact Tonelli representation.

import Mathlib
open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneRationalLintegralToReal :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal ((1 + a ^ 2)⁻¹)).toReal =
    (∫ a in Ioi (0 : ℝ), (1 + a ^ 2)⁻¹) := by
  sorry
