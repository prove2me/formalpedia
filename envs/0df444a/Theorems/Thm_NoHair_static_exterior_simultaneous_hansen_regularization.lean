-- Prove2me | Theorems.Thm_NoHair_static_exterior_simultaneous_hansen_regularization
-- name    : NoHair.static_exterior_simultaneous_hansen_regularization
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:28:53.801341+00:00
-- url     : https://prove2.me/theorems/6d1587af-e8af-40f1-a750-c41d55aa27f4
-- title:
--   Simultaneous smooth regularization of the static quotient metric and its potential at infinity
-- statement:
--   For positive-mass static vacuum data outside a coordinate ball, regularize the compactified quotient metric and squared lapse ratio in one chart at spatial infinity. The quotient metric here is Ω²N²h with Ω=(N⁻¹−N)²/4. An initial smooth punctured chart already puts (1−N)/(1+N) equal to the radius. A coordinate change at the puncture may be necessary for joint metric and potential regularity. The hypotheses concern only the data outside a compact set.
-- source:
--   R. Beig and W. Simon, Proof of a multipole conjecture due to Geroch, Comm. Math. Phys. 78 (1980), 75–82, https://doi.org/10.1007/BF01941970. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. These statements concern the lapse and its radial coordinate near the compactified end.

import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff

theorem NoHair.static_exterior_simultaneous_hansen_regularization (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (R μ : ℝ) (hR : 0<R) (hm : 0<μ)
    (inside : ∀ x : ADMPoint, R<‖x‖ → x∈Ω) (mono : HasStaticLapseMonopole N μ)
    (positive : ∀ x : ADMPoint, R<‖x‖ → 0<N x ∧ N x<1 ∧ (h x).PosDef)
    (smooth : ∀ x : ADMPoint, R<‖x‖ → ContDiffAt ℝ ∞ N x ∧ ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (falloff : ∀ k : ℕ, ∃ L C : ℝ, 0<L ∧ 0<C ∧ ∀ x : ADMPoint, L<‖x‖ →
      ‖iteratedFDeriv ℝ k (fun y => N y-1) x‖ ≤ C/‖x‖^(k+1) ∧
      ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖ ≤ C/‖x‖^(k+1))
    (equations : ∀ x : ADMPoint, R<‖x‖ →
      (∀ i j : Fin 3, staticSpatialHessian N h i j x = N x * spatialRicciTensor h x i j) ∧
      (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian N h i j x) = 0)
    (radial : ∃ (δ : ℝ) (e : OpenPartialHomeomorph ADMPoint ADMPoint), 0 < δ ∧
      e.source = ball 0 δ ∩ ({0} : Set ADMPoint)ᶜ ∧ e.target ⊆ Ω ∧
      (∃ R : ℝ, ∀ x : ADMPoint, R < ‖x‖ → x ∈ e.target) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      Tendsto (fun y : ADMPoint => ‖e y‖) (𝓝[≠] 0) atTop ∧
      Tendsto (fun x : ADMPoint => e.symm x) (cocompact ADMPoint) (𝓝 0) ∧
      ∀ y ∈ e.source, (1-N (e y))/(1+N (e y)) = ‖y‖) :
    ∃ (a : StaticMinusPointChart Ω N (fun x : ADMPoint => (((1+N x)^4)/(N x)^2) • h x)) (b : ADMPoint → ℝ),
      b 0 = 0 ∧ ContDiffOn ℝ ∞ b (ball 0 a.radius) ∧ (∀ y ∈ ball 0 a.radius, b y < 1) ∧
      ∀ y ∈ a.change.source, 0 < N (a.change y) ∧
        b y = ((1-N (a.change y))/(1+N (a.change y)))^2 := by
  sorry
