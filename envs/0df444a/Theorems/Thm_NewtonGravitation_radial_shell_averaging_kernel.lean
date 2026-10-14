-- Prove2me | Theorems.Thm_NewtonGravitation_radial_shell_averaging_kernel
-- name    : NewtonGravitation.radial_shell_averaging_kernel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T12:25:21.332612+00:00
-- url     : https://prove2.me/theorems/cc7656ae-2dd5-4c60-8736-18922736283f
-- title:
--   Angular integration of the Newton kernel as a radial shell integral
-- statement:
--   For a finite spherically symmetric mass measure μ on Euclidean three-space, let ν be the radial pushforward of μ under y↦‖y‖. If the Newtonian gravitational field kernel is Bochner integrable at x, then angular integration over spherical mass layers converts the gravitational field into the integral against ν of the following explicit radial kernel: the vector −Gx/‖x‖³ for radii strictly below ‖x‖, and zero for radii at or above ‖x‖. The integrability assumption controls any mass on the singular observation sphere and justifies exchanging angular and radial integration. This isolates the substantive Newton shell-averaging calculation; the remaining parent enclosed-mass identity follows from elementary indicator integration and the definition of the radial pushforward.
-- source:
--   Newton's Law of Universal Gravitation: the Shell Theorem, Prove2Me mission, spherical symmetry and enclosed mass statement, https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.radial_shell_averaging_kernel
    (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsSphericallySymmetric μ) (x : Space)
    (hint : Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ) :
    gravField μ x =
      ∫ r : ℝ, (if r < ‖x‖ then (-(G / ‖x‖ ^ 3)) • x else 0)
        ∂(μ.map (fun y : Space => ‖y‖)) := by sorry
