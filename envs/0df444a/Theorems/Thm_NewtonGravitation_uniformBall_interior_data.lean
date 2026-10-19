-- Prove2me | Theorems.Thm_NewtonGravitation_uniformBall_interior_data
-- name    : NewtonGravitation.uniformBall_interior_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T12:18:34.808808+00:00
-- url     : https://prove2.me/theorems/d346794a-3d91-4751-8304-38b5fb5c7ee5
-- title:
--   Uniform solid ball: interior enclosed mass and integrability
-- statement:
--   For a uniform mass distribution of total mass M throughout a three-dimensional solid ball of positive radius R, the induced measure is finite and invariant under rotations. For every interior observation point x, the Newtonian inverse-square kernel is integrable against the ball's volume density, and the mass enclosed within radius ‖x‖ is M times the ratio of volumes, namely (‖x‖/R)^3. At x=0 this enclosed mass vanishes, and the formula remains valid. The identities supply analytic and geometric hypotheses for the general enclosed-mass theorem without assuming the desired gravitational field formula.
-- source:
--   Prove2Me Newton's Law of Universal Gravitation: the Shell Theorem, uniformBall definition and interior field milestone, https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.uniformBall_interior_data (M : NNReal) (R : ℝ)
    (hR : 0 < R) (x : Space) (hx : ‖x‖ < R) :
    IsFiniteMeasure (uniformBall M R) ∧
      IsSphericallySymmetric (uniformBall M R) ∧
      Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) (uniformBall M R) ∧
      (uniformBall M R).real (Metric.ball (0 : Space) ‖x‖) =
        (M : ℝ) * (‖x‖ / R) ^ 3 := by sorry
