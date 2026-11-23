-- Prove2me | Theorems.Thm_NoHair_inverse_radius_limit_of_decaying_poisson_field
-- name    : NoHair.inverse_radius_limit_of_decaying_poisson_field
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:18:58.545092+00:00
-- url     : https://prove2.me/theorems/56da97b4-f595-4817-9e67-2c7843cd680c
-- title:
--   Direction-independent inverse-radius coefficient of a three-dimensional Poisson field
-- statement:
--   A decaying Poisson field on three-dimensional Euclidean space with an integrable inverse-quartic source has a uniform inverse-radius coefficient at infinity. The coefficient is the integral of the negative Laplacian divided by the area of the unit sphere.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. J. K. Hunter, Notes on Partial Differential Equations, Chapter 2 (spherical means and the divergence theorem), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. The rescaled-ball formula and its estimate here give the leading three-dimensional lapse coefficient.

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem NoHair.inverse_radius_limit_of_decaying_poisson_field (u : ADMPoint → ℝ) (hu : ContDiff ℝ 2 u)
    (h0 : Tendsto u (cocompact ADMPoint) (𝓝 0))
    (hi : Integrable (fun z => -(Δ u) z))
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ u) z| ≤ C/‖z‖^4) :
    Tendsto (fun x : ADMPoint => ‖x‖*u x) (cocompact ADMPoint)
      (𝓝 ((∫ z, -(Δ u) z)/(3*volume.real (ball (0:ADMPoint) 1)))) := by
  sorry
