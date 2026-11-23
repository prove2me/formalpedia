-- Prove2me | Theorems.Thm_NoHair_rescaled_ball_mass_recovers_total_source
-- name    : NoHair.rescaled_ball_mass_recovers_total_source
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:18:57.94481+00:00
-- url     : https://prove2.me/theorems/8a881d8d-9c31-4a9b-9dbb-8f5bb7fb7849
-- title:
--   Rescaled translated balls recover the total Poisson source at infinity
-- statement:
--   For a three-dimensional integrable source with inverse-quartic decay, integrate the mass of the ball centered at x with radius t|x| against dt/t². As |x| tends to infinity the integral tends to the total source. For t below one each fixed source point eventually lies outside the ball, and for t above one it eventually lies inside. Decay controls the singular weight at t=0.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. J. K. Hunter, Notes on Partial Differential Equations, Chapter 2 (spherical means and the divergence theorem), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. The rescaled-ball formula and its estimate here give the leading three-dimensional lapse coefficient.

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem NoHair.rescaled_ball_mass_recovers_total_source (q : ADMPoint → ℝ) (hi : Integrable q)
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |q z| ≤ C/‖z‖^4) :
    Tendsto (fun x : ADMPoint => (∫ t : ℝ in Ioi 0, (∫ z in ball x (t*‖x‖), q z)/t^2)) (cocompact ADMPoint) (𝓝 (∫ z, q z)) := by
  sorry
