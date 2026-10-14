-- Prove2me | Theorems.Thm_NewtonGravitation_shell_angular_primitive_deriv
-- name    : NewtonGravitation.shell_angular_primitive_deriv
-- status  : Open
-- author  : @WillR
-- created : 2026-10-14T07:04:40.291469+00:00
-- url     : https://prove2.me/theorems/a28bcd9d-4391-40e6-bb68-54e5c9151749
-- title:
--   Derivative of the exact Newton spherical-shell angular primitive
-- statement:
--   For observation radius R>0, shell radius r>0, and parameter t where D(t)=R²+r²−2Rrt is positive, the derivative of J(t)=((R²−r²)/√D(t)−√D(t))/(4R²r) equals (R−rt)/(2(√D(t))³). Applying the fundamental theorem of calculus and the companion endpoint lemma yields the angular average of the Newtonian inverse-square field away from the singular radius.
-- source:
--   Prove2Me Newton's Law of Universal Gravitation: the Shell Theorem; direct differentiation of a shell-integral antiderivative.

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open NewtonGravitation

theorem NewtonGravitation.shell_angular_primitive_deriv
    (R r t : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hD : 0 < R ^ 2 + r ^ 2 - 2 * R * r * t) :
    HasDerivAt
      (fun u : ℝ =>
        ((R ^ 2 - r ^ 2) / Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * u) -
          Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * u)) / (4 * R ^ 2 * r))
      ((R - r * t) /
        (2 * (Real.sqrt (R ^ 2 + r ^ 2 - 2 * R * r * t)) ^ 3)) t := by sorry
