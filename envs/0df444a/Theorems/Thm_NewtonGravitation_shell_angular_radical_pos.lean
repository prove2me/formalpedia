-- Prove2me | Theorems.Thm_NewtonGravitation_shell_angular_radical_pos
-- name    : NewtonGravitation.shell_angular_radical_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-14T07:06:20.565156+00:00
-- url     : https://prove2.me/theorems/f464cf12-db3a-49c1-889c-a7637d3e8a7c
-- title:
--   Positivity of the Newton spherical angular denominator away from the singular shell
-- statement:
--   For R>0, shell radius r≥0 with r≠R and cosine parameter t≤1, the squared distance D(t)=R²+r²−2Rrt is strictly positive. Indeed D(t)=(R−r)²+2Rr(1−t), where the first term is strictly positive and the second nonnegative. This guarantees the square-root denominator in the angular primitive stays nonzero on the integration interval [-1,1] whenever the observation and shell radii differ.
-- source:
--   Prove2Me Newton's Law of Universal Gravitation: the Shell Theorem, spherical angular kernel positivity.

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open NewtonGravitation

theorem NewtonGravitation.shell_angular_radical_pos
    (R r t : ℝ) (hR : 0 < R) (hr : 0 ≤ r)
    (hne : r ≠ R) (ht : t ≤ 1) :
    0 < R ^ 2 + r ^ 2 - 2 * R * r * t := by sorry
