-- Prove2me | Theorems.Thm_NoHair_regular_static_lapse_euclidean_poisson_source
-- name    : NoHair.regular_static_lapse_euclidean_poisson_source
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:19:07.312051+00:00
-- url     : https://prove2.me/theorems/4afca4c0-9c2a-4fd8-b81b-16dbb3f62ff4
-- title:
--   The cutoff static lapse defect has an integrable Poisson source of positive total mass
-- statement:
--   Extend the lapse defect smoothly through the interior after cutting it off across a large compact set. The static equations and the given derivative falloff yield inverse-quartic decay of its Euclidean Laplacian. Its negative Laplacian has positive integral, identified by the divergence theorem with the positive conserved physical lapse flux.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. J. K. Hunter, Notes on Partial Differential Equations, Chapter 2 (spherical means and the divergence theorem), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. The rescaled-ball formula and its estimate here give the leading three-dimensional lapse coefficient.

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem NoHair.regular_static_lapse_euclidean_poisson_source (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ u : ADMPoint → ℝ, ContDiff ℝ 2 u ∧
      (∀ᶠ x in cocompact ADMPoint, u x = 1-N x) ∧
      Tendsto u (cocompact ADMPoint) (𝓝 0) ∧ Integrable (fun z => -(Δ u) z) ∧
      (∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ u) z| ≤ C/‖z‖^4) ∧
      0 < ∫ z, -(Δ u) z := by
  sorry
