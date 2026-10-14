-- Prove2me | Theorems.Thm_NewtonGravitation_integrable_newtonKernel_inside_hollow
-- name    : NewtonGravitation.integrable_newtonKernel_inside_hollow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T12:20:52.048951+00:00
-- url     : https://prove2.me/theorems/01579bdd-8895-4cdc-a269-54d10a10e73d
-- title:
--   Newtonian kernel integrable inside a mass-free spherical cavity
-- statement:
--   Suppose a finite measure on three-dimensional Euclidean space gives no mass to the open ball of radius ρ. At any point x satisfying ‖x‖<ρ, the Newtonian gravitational acceleration kernel is Bochner integrable. The gap δ=ρ−‖x‖>0 bounds the distance ‖x−y‖ from below by δ at μ-almost every y. Consequently the inverse-square force magnitude is bounded μ-almost everywhere, and finite total mass guarantees integrability. This analytic lemma is independent of spherical symmetry and supplies the missing integrability hypothesis for the interior shell theorem.
-- source:
--   Prove2Me Newton's Law of Universal Gravitation: the Shell Theorem, general interior shell theorem milestone and formalization note, https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.integrable_newtonKernel_inside_hollow
    (μ : Measure Space) [IsFiniteMeasure μ] (ρ : ℝ)
    (hρ : μ (Metric.ball (0 : Space) ρ) = 0)
    (x : Space) (hx : ‖x‖ < ρ) :
    Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ := by sorry
