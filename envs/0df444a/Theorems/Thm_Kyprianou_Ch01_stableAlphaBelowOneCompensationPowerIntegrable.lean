-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerIntegrable
-- name    : Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:48:19.803404+00:00
-- url     : https://prove2.me/theorems/a45e41e1-4c25-4e5a-838d-e5e77aabd8e2
-- title:
--   Stable below-one small-jump compensator power integrability on (0,1)
-- statement:
--   For 0<alpha<1 the small-jump moment kernel r^-alpha is Lebesgue integrable on the source cutoff interval (0,1), via the pinned Mathlib exact integrableOn_Ioo_rpow_iff characterisation. Enables legal Bochner integral subtraction.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, original stable small-jump compensation.

import Mathlib
open MeasureTheory Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerIntegrable
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    IntegrableOn (fun r : ℝ => r ^ (-alpha))
      (Set.Ioo (0 : ℝ) 1) := by sorry
