-- Prove2me | Theorems.Thm_NoHair_static_riemannian_gluing_with_continuous_pole
-- name    : NoHair.static_riemannian_gluing_with_continuous_pole
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:54:05.798926+00:00
-- url     : https://prove2.me/theorems/1ccbd9af-cd66-49ee-a273-3e570d7a5b2b
-- title:
--   Smooth gluing and completion of the static conformal double from a nondegenerate continuous pole
-- statement:
--   Starting from a regular static end with the positive-sheet mass and completeness estimates and horizon matching data, suppose the inverted negative sheet has already acquired its continuous positive-definite value at its end. Establish the smooth geometric completion, including regularity at the horizon seam and the filled point, and the signed lapse equation required by the doubling theorem. A smooth chart compatible with the geometric completion must be justified.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154. https://doi.org/10.1007/BF00770326. Here the negative sheet uses unit Euclidean inversion and the coefficient of the inverse-radius term of the lapse.

import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter
open scoped Topology ContDiff

theorem NoHair.static_riemannian_gluing_with_continuous_pole (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (hflat : ∀ x ∈ closure Ω, spatialScalarCurvature h x = 0 ∧
      ∀ s : ℝ, 1 + s * N x ≠ 0 →
        spatialScalarCurvature (staticPositiveMetric (fun y => s*N y) h) x = 0)
    (hforms : ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ frontier Ω, ∀ s : ℝ, s = 1 ∨ s = -1 →
      let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := staticPositiveMetric (fun y => s*N y) h
      (∀ i j : Fin 3, k x i j = h x i j / 16) ∧
      staticLapseGradientSq N k x = (4*κ)^2 ∧
      ∀ v w : ADMPoint, fderiv ℝ N x v = 0 → fderiv ℝ N x w = 0 →
        (∑ i : Fin 3, ∑ j : Fin 3, staticSpatialHessian N k i j x * v i * w j) / (4*κ) =
          s*8*κ*(∑ i : Fin 3, ∑ j : Fin 3, k x i j * v i * w j))
    (μ : ℝ) (hμ : 0 < μ) (hpole : HasContinuousStaticPole N h μ) :
    Nonempty (StaticConformalCompletion Ω N h) := by
  sorry
