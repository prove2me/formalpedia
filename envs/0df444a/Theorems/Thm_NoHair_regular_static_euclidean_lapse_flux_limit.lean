-- Prove2me | Theorems.Thm_NoHair_regular_static_euclidean_lapse_flux_limit
-- name    : NoHair.regular_static_euclidean_lapse_flux_limit
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:26:27.532364+00:00
-- url     : https://prove2.me/theorems/22e4d670-9057-4370-ac7e-0d521ee94d83
-- title:
--   The Euclidean lapse flux tends to the positive conserved physical flux
-- statement:
--   The inverse metric density tends to the identity, while the rescaled first derivatives of the lapse remain bounded. The difference of the Euclidean flux and the conserved geometric flux therefore tends to zero.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. J. K. Hunter, Notes on Partial Differential Equations, Chapter 2 (spherical means and the divergence theorem), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. The rescaled-ball formula and its estimate here give the leading three-dimensional lapse coefficient.

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem NoHair.regular_static_euclidean_lapse_flux_limit (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ m : ℝ, 0 < m ∧ Tendsto (fun r : ℝ => r^2 *
      ∫ n : ADMSphere, fderiv ℝ N (r • (n:ADMPoint)) (n:ADMPoint) ∂admSurfaceMeasure) atTop (𝓝 m) := by
  sorry
