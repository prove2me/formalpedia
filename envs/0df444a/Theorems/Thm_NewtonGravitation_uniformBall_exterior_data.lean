-- Prove2me | Theorems.Thm_NewtonGravitation_uniformBall_exterior_data
-- name    : NewtonGravitation.uniformBall_exterior_data
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T12:08:42.276539+00:00
-- url     : https://prove2.me/theorems/80d426e2-8f12-40ec-b3ea-446b690bed8c
-- title:
--   Uniform ball: finite radial mass, enclosed mass and kernel integrability at the boundary
-- statement:
--   Consider the uniform solid ball of mass $M\ge0$ and positive radius $R$ in Euclidean three-space. For every observation point $x$ with $\|x\|\ge R$, the corresponding mass measure is finite and spherically symmetric. Its enclosed mass within the open ball of radius $\|x\|$ equals $M$:
--
--   $$\sigma_{M,R}(B(0,\|x\|))=M.$$
--
--   Moreover the Newtonian inverse-square field kernel is Bochner integrable against the uniform solid-ball measure, including when $\|x\|=R$. At a boundary point, local integrability follows from the three-dimensional volume element cancelling the order-two kernel singularity. This combines the measure-theoretic hypotheses needed for the exterior uniform-ball field formula, separately from the substantive shell-theorem integral identity.
-- source:
--   Prove2Me, Newton's Law of Universal Gravitation: the Shell Theorem, Uniform solid sphere milestone and Formalization scope (Bochner integrability at singular points), https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.uniformBall_exterior_data (M : NNReal) (R : ℝ) (hR : 0 < R)
    (x : Space) (hx : R ≤ ‖x‖) :
    IsFiniteMeasure (uniformBall M R) ∧
      IsSphericallySymmetric (uniformBall M R) ∧
      Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) (uniformBall M R) ∧
      (uniformBall M R).real (Metric.ball (0 : Space) ‖x‖) = (M : ℝ) := by sorry
