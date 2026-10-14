-- Prove2me | Theorems.Thm_NewtonGravitation_shell_angular_endpoints
-- name    : NewtonGravitation.shell_angular_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-14T07:00:13.414977+00:00
-- url     : https://prove2.me/theorems/44de47af-e016-4602-b628-cba19baa0b0c
-- title:
--   Exact angular primitive endpoints for the Newton shell kernel
-- statement:
--   Let R>0 be the observation radius and r>0 a distinct shell radius. The antiderivative J(t)=((R²−r²)/sqrt(R²+r²−2Rrt)−sqrt(R²+r²−2Rrt))/(4R²r) has endpoints J(1) and J(−1) represented by the respective absolute values |R−r| and |R+r|. Their exact difference is 1/R² for r<R and zero for r>R. This elementary identity supplies the endpoint algebra after the fundamental theorem of calculus in the radial shell-averaging proof.
-- source:
--   Prove2Me Newton's Law of Universal Gravitation: the Shell Theorem; explicit integration of the spherical Newtonian kernel.

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open NewtonGravitation

theorem NewtonGravitation.shell_angular_endpoints (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hne : r ≠ R) :
    ((R ^ 2 - r ^ 2) / |R - r| - |R - r|) / (4 * R ^ 2 * r) -
      ((R ^ 2 - r ^ 2) / |R + r| - |R + r|) / (4 * R ^ 2 * r) =
      if r < R then 1 / R ^ 2 else 0 := by sorry
