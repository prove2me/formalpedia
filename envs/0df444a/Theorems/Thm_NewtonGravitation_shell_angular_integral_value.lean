-- Prove2me | Theorems.Thm_NewtonGravitation_shell_angular_integral_value
-- name    : NewtonGravitation.shell_angular_integral_value
-- status  : Open
-- author  : @WillR
-- created : 2026-10-14T07:18:10.170909+00:00
-- url     : https://prove2.me/theorems/96d45708-c9a9-4c7e-8504-41e4703831d0
-- title:
--   Exact Newtonian angular integral for an off-radius spherical shell
-- statement:
--   For observation radius R>0 and a nonzero shell radius r>0 distinct from R, the angular integral over cosθ from −1 to 1 of the axial inverse-square Newtonian kernel equals 1/R² when the shell lies inside the observation radius, and zero when the shell lies outside it. The proof uses the antiderivative derivative, positivity of the squared-distance denominator and exact endpoint algebra. This is the essential analytic scalar step toward the full Newtonian shell theorem; it does not assert arbitrary rotationally invariant measure disintegration.
-- source:
--   Prove2Me Newton's Law of Universal Gravitation: the Shell Theorem; exact evaluation of the axial spherical average of 1/|x−y|³.

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.shell_angular_integral_value
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hne : r ≠ R) :
    (∫ t in (-1 : ℝ)..1,
        (R - r * t) /
          (2 * (Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * t)) ^ 3)) =
      if r < R then 1 / R ^ 2 else 0 := by sorry
