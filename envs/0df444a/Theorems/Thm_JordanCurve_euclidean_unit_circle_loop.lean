-- Prove2me | Theorems.Thm_JordanCurve_euclidean_unit_circle_loop
-- name    : JordanCurve.euclidean_unit_circle_loop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T13:15:21.029744+00:00
-- url     : https://prove2.me/theorems/5594dc96-d4b7-4813-9fc1-ed94eeb4e5dd
-- title:
--   Once-around parametrization of the Euclidean unit circle
-- statement:
--   There is a continuous path on [0,1] traversing the unit circle completely, meeting no point twice on [0,1), and returning to its starting point at time 1. An explicit construction transports the complex exponential t ↦ exp(i(2πt−π)) by the standard isometry from the complex plane to Euclidean two-space.
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace JordanCurve

/-- A continuous once-around traversal of the Euclidean unit circle. -/
theorem euclidean_unit_circle_loop :
    ∃ e : ℝ → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ContinuousOn e (Set.Icc 0 1) ∧ e 0 = e 1 ∧
      Set.InjOn e (Set.Ico 0 1) ∧ e '' Set.Icc 0 1 = Set.univ := by sorry

end JordanCurve
