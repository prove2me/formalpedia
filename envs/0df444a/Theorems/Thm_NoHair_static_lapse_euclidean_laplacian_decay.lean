-- Prove2me | Theorems.Thm_NoHair_static_lapse_euclidean_laplacian_decay
-- name    : NoHair.static_lapse_euclidean_laplacian_decay
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:26:11.221735+00:00
-- url     : https://prove2.me/theorems/7ab54049-5e75-4bc8-95a8-513a6221edf0
-- title:
--   Inverse-quartic Euclidean Laplacian decay of a regular static lapse
-- statement:
--   The time-time static Ricci component is the lapse times its metric Laplacian, which vanishes by the static equations. Compare with the Euclidean principal term in the asymptotic Cartesian Ricci expansion to gain an extra inverse power of the radius.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. J. K. Hunter, Notes on Partial Differential Equations, Chapter 2 (spherical means and the divergence theorem), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. The rescaled-ball formula and its estimate here give the leading three-dimensional lapse coefficient.

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem NoHair.static_lapse_euclidean_laplacian_decay (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ N) z| ≤ C/‖z‖^4 := by
  sorry
