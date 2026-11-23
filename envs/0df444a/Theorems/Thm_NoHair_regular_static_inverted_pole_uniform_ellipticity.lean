-- Prove2me | Theorems.Thm_NoHair_regular_static_inverted_pole_uniform_ellipticity
-- name    : NoHair.regular_static_inverted_pole_uniform_ellipticity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:32:47.879884+00:00
-- url     : https://prove2.me/theorems/ee27a2c0-7e05-421b-8d99-9708e84e9a5b
-- title:
--   Uniformly positive metric at the compactified end of every regular static slice
-- statement:
--   The lapse defect on any regular static end has a strictly positive monopole. Unit inversion therefore makes the negative-sheet metric continuous and uniformly positive near the puncture. The bounds apply to every tangent vector with constants expressed in terms of the monopole.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. J. K. Hunter, Notes on Partial Differential Equations, Chapter 2 (spherical means and the divergence theorem), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. The rescaled-ball formula and its estimate here give the leading three-dimensional lapse coefficient.

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem NoHair.regular_static_inverted_pole_uniform_ellipticity (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ μ δ : ℝ, 0 < μ ∧ 0 < δ ∧ HasStaticLapseMonopole N μ ∧
      HasContinuousStaticPole N h μ ∧ ∀ y : ADMPoint, 0 < ‖y‖ → ‖y‖ < δ →
      ∀ v : ADMPoint,
        let Q := ∑ i : Fin 3, ∑ j : Fin 3, staticInvertedNegativeMetric N h y i j * v i * v j
        (μ/2)^4/2 * ‖v‖^2 ≤ Q ∧ Q ≤ 2*(μ/2)^4 * ‖v‖^2 := by
  sorry
