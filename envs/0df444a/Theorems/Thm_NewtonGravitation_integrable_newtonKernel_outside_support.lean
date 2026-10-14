-- Prove2me | Theorems.Thm_NewtonGravitation_integrable_newtonKernel_outside_support
-- name    : NewtonGravitation.integrable_newtonKernel_outside_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T11:58:54.335123+00:00
-- url     : https://prove2.me/theorems/15a8f9aa-e19d-41c5-98b4-cf8014ea50a1
-- title:
--   Integrability of Newton's field kernel outside bounded mass support
-- statement:
--   Let $\mu$ be a finite Borel mass measure on Euclidean three-space, supported in the closed ball of radius $R$ about the origin. If the field point $x$ satisfies $\|x\|>R$, the Newtonian gravitational field kernel is Bochner integrable with respect to $\mu$:
--
--   $$\int \left\|\frac{-G(x-y)}{\|x-y\|^3}\right\|\,d\mu(y)<\infty.$$
--
--   The positive separation between the observation point and the support ensures the singularity at $y=x$ is avoided. This is the analytic integrability hypothesis needed to apply the enclosed-mass shell theorem to an exterior point.
-- source:
--   Prove2Me, Newton's Law of Universal Gravitation: the Shell Theorem, Shell theorem exterior and Formalization scope (integrability outside support), https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.integrable_newtonKernel_outside_support
    (μ : Measure Space) [IsFiniteMeasure μ] (R : ℝ)
    (hR : μ (Metric.closedBall (0 : Space) R)ᶜ = 0)
    (x : Space) (hx : R < ‖x‖) :
    Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ := by sorry
