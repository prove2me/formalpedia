-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_geometric_potential_from_scale_public
-- name    : Kyprianou.Ch08.StageB.p2m81_geometric_potential_from_scale_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T18:48:36.030184+00:00
-- url     : https://prove2.me/theorems/daa25b4f-edc3-49f1-bd17-0928e44941e8
-- title:
--   One-scale renewal potential with exact positive atom formula
-- statement:
--   Fix a positive scale d and a probability drawdown law satisfying the Chapter 8 cross-multiplied identity. Build the nonnegative tail kernel with density d rho((x,infinity)) on x>0. Its total mass is at most one and its Laplace transform is d(1-Lrho(s))/s. The geometric renewal package with discount one half, followed by convolution with rho and scaling by 2d/f(d), gives a potential supported on the nonnegative half-line, finite on lower intervals, with Laplace transform s/f(s). Its only positive atoms come from the renewal zeroth term, giving the exact singleton mass d/f(d) times rho{x}.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Public helper for the geometric descending potential, one-scale renewal construction.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_geometric_potential_from_scale_public
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0)
    (hdraw : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d)) :
    ∃ ν : Measure ℝ,
      ν (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
          ENNReal.ofReal (s / f s)) ∧
      (∀ x : ℝ, 0 < x →
        ν {x} = ENNReal.ofReal (d / f d) * ρ {x}) := by
  sorry
