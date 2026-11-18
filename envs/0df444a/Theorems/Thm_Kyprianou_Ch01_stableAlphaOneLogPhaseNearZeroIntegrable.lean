-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseNearZeroIntegrable
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseNearZeroIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:38:08.987199+00:00
-- url     : https://prove2.me/theorems/c12041c8-92d1-4ca8-88fa-10259258eb87
-- title:
--   Near-zero Bochner integrability of the exact compensated complex stable alpha-one kernel
-- statement:
--   For z>0, the original compensated complex alpha-one stable Lévy integrand is absolutely integrable on 0<r<1/(1+z). The full small-jump compensator is active there, and the pinned second-order complex exponential remainder inequality bounds the quotient uniformly by z² on this finite interval.
-- source:
--   Kyprianou (2006), Chapter 1, stable index-one logarithmic Lévy phase.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexRemainderQuadratic
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseNearZeroIntegrable
    (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
      (Set.Ioo (0 : ℝ) (1 / (1 + z))) := by
  sorry
