-- Prove2me | Theorems.Thm_NoHair_spherical_mean_lapse_source_identity
-- name    : NoHair.spherical_mean_lapse_source_identity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:18:51.331801+00:00
-- url     : https://prove2.me/theorems/13fa562e-f25e-4af5-8d96-ebd16235f896
-- title:
--   The rescaled spherical mean expresses the exterior field through masses of translated balls
-- statement:
--   For a decaying twice differentiable field with integrable inverse-quartic Laplacian, differentiate its spherical mean around x at radius t|x| and integrate from t=0 to infinity. This represents the rescaled field as the weighted integral of the Poisson source over translated balls.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. J. K. Hunter, Notes on Partial Differential Equations, Chapter 2 (spherical means and the divergence theorem), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. The rescaled-ball formula and its estimate here give the leading three-dimensional lapse coefficient.

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

theorem NoHair.spherical_mean_lapse_source_identity (u : ADMPoint → ℝ) (hu : ContDiff ℝ 2 u)
    (h0 : Tendsto u (cocompact ADMPoint) (𝓝 0))
    (hi : Integrable (fun z => -(Δ u) z))
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |(Δ u) z| ≤ C/‖z‖^4) :
    ∀ᶠ x : ADMPoint in cocompact ADMPoint, (3*volume.real (ball (0:ADMPoint) 1))*‖x‖*u x =
      (∫ t : ℝ in Ioi 0, (∫ z in ball x (t*‖x‖), -(Δ u) z)/t^2) := by
  sorry
