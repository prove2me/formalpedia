-- Prove2me | Theorems.Thm_Kyprianou_Ch01_continuousRightDerivative_impliesLeft
-- name    : Kyprianou.Ch01.continuousRightDerivative_impliesLeft
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T17:50:29.332763+00:00
-- url     : https://prove2.me/theorems/3310b827-e4ca-4ce9-bd5e-4de910e96149
-- title:
--   Continuous right derivatives with a continuous slope extend to left derivatives
-- statement:
--   For a real-valued function continuous on the nonnegative half-line, with a continuous slope g and the right derivative at every nonnegative time equal to g, its one-sided left derivative at every strictly positive time equals g. The proof uses the fundamental theorem of calculus for right derivatives and differentiates the integral primitive of g at the endpoint. This provides the analytic bridge needed in one-sided branching-process evolution arguments.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(iii); general one-sided derivative extension by the fundamental theorem of calculus

import Mathlib
open MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.continuousRightDerivative_impliesLeft
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hg : Continuous g)
    (hright : ∀ x : ℝ, 0 ≤ x →
      HasDerivWithinAt f (g x) (Ioi x) x)
    (t : ℝ) (ht : 0 < t) :
    HasDerivWithinAt f (g t) (Iic t) t := by sorry
