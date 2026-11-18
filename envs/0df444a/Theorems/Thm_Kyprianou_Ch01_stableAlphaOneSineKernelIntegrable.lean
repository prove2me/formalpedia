-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneSineKernelIntegrable
-- name    : Kyprianou.Ch01.stableAlphaOneSineKernelIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:09:51.063867+00:00
-- url     : https://prove2.me/theorems/167645ff-45ad-4dd4-a2b1-4bff0acfdb73
-- title:
--   Absolute integrability of the compensated sine alpha-one stable Lévy kernel
-- statement:
--   For every positive frequency z, the exact compensated real sine integrand (zr·1_(r<1)−sin(zr))/r² is Lebesgue integrable over (0,∞). This follows from the Proved integrability of the source complex compensated stable kernel and its exact pointwise imaginary-part identity.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable Lévy exponent.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseIntegrableExact
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImagKernel
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneSineKernelIntegrable
    (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r : ℝ =>
      ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  sorry
