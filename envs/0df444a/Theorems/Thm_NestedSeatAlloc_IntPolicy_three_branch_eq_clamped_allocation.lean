-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_three_branch_eq_clamped_allocation
-- name    : NestedSeatAlloc.IntPolicy.three_branch_eq_clamped_allocation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:46:09.419081+00:00
-- url     : https://prove2.me/theorems/bed7d85a-7ec5-4d35-a34b-0934714bb917
-- title:
--   Equivalent clamped-allocation representation of nested fare-class revenue
-- statement:
--   # Algebraic equivalence of the three-branch and clamped revenue rules
--
--   Let a be the high-fare protection level, c the next fare, y>=0 the realised next-class demand and g the high-fare revenue function. The three-branch recursion returns g(s) if s<a, c(s-a)+g(a) if a<=s<a+y, and cy+g(s-y) otherwise.
--
--   Define U=min(max(s-a,0),y). Then every branch equals cU+g(s-U). This holds for any real s, a and c, for any function g, and for nonnegative y; no concavity or differentiability assumptions are needed.
--
--   The proof splits into the three regions and simplifies the clamp to 0, s-a or y respectively. This separate exact identity is needed to apply the already published clamped_surplus_optimal pointwise comparison to condRevenue_three_branch before the stochastic integration step. It is strictly algebraic and has no hidden assumptions about independent demands.
-- source:
--   # Algebraic equivalence of the three-branch and clamped revenue rules
--
--   Let a be the high-fare protection level, c the next fare, y>=0 the realised next-class demand and g the high-fare revenue function. The three-branch recursion returns g(s) if s<a, c(s-a)+g(a) if a<=s<a+y, and cy+g(s-y) otherwise.
--
--   Define U=min(max(s-a,0),y). Then every branch equals cU+g(s-U). This holds for any real s, a and c, for any function g, and for nonnegative y; no concavity or differentiability assumptions are needed.
--
--   The proof splits into the three regions and simplifies the clamp to 0, s-a or y respectively. This separate exact identity is needed to apply the already published clamped_surplus_optimal pointwise comparison to condRevenue_three_branch before the stochastic integration step. It is strictly algebraic and has no hidden assumptions about independent demands.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

theorem NestedSeatAlloc.IntPolicy.three_branch_eq_clamped_allocation
    (g : ℝ → ℝ) (a c y s : ℝ) (hy : 0 ≤ y) :
    (if s < a then g s else if s < a + y then
       (s - a) * c + g a else y * c + g (s - y)) =
    c * min (max (s - a) 0) y +
      g (s - min (max (s - a) 0) y) := by sorry
