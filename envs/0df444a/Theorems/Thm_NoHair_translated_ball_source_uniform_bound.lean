-- Prove2me | Theorems.Thm_NoHair_translated_ball_source_uniform_bound
-- name    : NoHair.translated_ball_source_uniform_bound
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:20:01.161326+00:00
-- url     : https://prove2.me/theorems/a72f8fb9-c161-4919-9310-cc23f66947f5
-- title:
--   Uniform integrable bound for the masses of translated balls at every scale
-- statement:
--   When t is at most one half, all points of the translated ball stay at least half the center radius from the origin. Decay of the source and the cubic volume law control the mass at these scales. At larger scales absolute integrability supplies a bound by the total absolute mass.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. J. K. Hunter, Notes on Partial Differential Equations, Chapter 2 (spherical means and the divergence theorem), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. The rescaled-ball formula and its estimate here give the leading three-dimensional lapse coefficient.

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem NoHair.translated_ball_source_uniform_bound (q : ADMPoint → ℝ) (hi : Integrable q)
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |q z| ≤ C/‖z‖^4) :
    ∃ K R : ℝ, 0 < K ∧ 0 < R ∧ ∀ x : ADMPoint, R < ‖x‖ → ∀ t : ℝ, 0 < t →
      |(∫ z in ball x (t*‖x‖), q z)/t^2| ≤ K/(t+1)^2 := by
  sorry
