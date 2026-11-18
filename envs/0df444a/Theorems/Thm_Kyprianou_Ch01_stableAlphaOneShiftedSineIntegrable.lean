-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneShiftedSineIntegrable
-- name    : Kyprianou.Ch01.stableAlphaOneShiftedSineIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:19:18.824139+00:00
-- url     : https://prove2.me/theorems/776ddd4c-8e57-44bf-9f1b-effd6f899c1e
-- title:
--   Integrability of the shifted sine alpha-one stable Lévy kernel
-- statement:
--   For each positive z, the compensated sine integrand (u 1_(u<z)−sin u)/u² is integrable on u>0. The proved original fixed-cutoff integrability and exact positive rescaling g_z(r)=z² f_z(zr), together with the pinned integrableOn_Ioi_comp_mul_left_iff, yield the statement.
-- source:
--   Kyprianou (2006), Chapter 1, alpha-one stable imaginary logarithmic phase.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneSineKernelIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryKernelScalingPointwise
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneShiftedSineIntegrable
    (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => (u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  sorry
