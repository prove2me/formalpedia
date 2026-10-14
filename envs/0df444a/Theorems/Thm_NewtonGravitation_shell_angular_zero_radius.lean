-- Prove2me | Theorems.Thm_NewtonGravitation_shell_angular_zero_radius
-- name    : NewtonGravitation.shell_angular_zero_radius
-- status  : Open
-- author  : @WillR
-- created : 2026-10-14T07:19:47.383816+00:00
-- url     : https://prove2.me/theorems/4c5fd553-3561-4e67-8394-87c6629eeb2c
-- title:
--   Newton angular integral of the zero-radius point mass layer
-- statement:
--   At positive observation radius R, the shell-average angular integrand for a shell radius of zero is independent of polar angle. Its integral from −1 to 1 is exactly 1/R². This supplies the r=0 endpoint case excluded by the nonzero-radius angular primitive formula and allows radial mixtures with an atom at the origin.
-- source:
--   Prove2Me Newton's Law of Universal Gravitation: the Shell Theorem; exact zero-radius angular average.

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.shell_angular_zero_radius (R : ℝ) (hR : 0 < R) :
    (∫ t in (-1 : ℝ)..1,
      R / (2 * (Real.sqrt (R ^ 2)) ^ 3)) = 1 / R ^ 2 := by sorry
