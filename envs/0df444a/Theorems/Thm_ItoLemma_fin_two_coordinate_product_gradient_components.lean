-- Prove2me | Theorems.Thm_ItoLemma_fin_two_coordinate_product_gradient_components
-- name    : ItoLemma.fin_two_coordinate_product_gradient_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:35:18.544581+00:00
-- url     : https://prove2.me/theorems/3a5d1c8b-1f88-4d9e-b92a-df9fdf20fb6b
-- title:
--   Coordinate Gradient of the Two-Dimensional Product
-- statement:
--   The partial derivatives of the product z₀z₁ are z₁ and z₀, represented by the coordinate-derivative operator used in the verified vector Itô formula. The derivative map is the one already established by the mission's Fréchet product derivative lemma.
-- source:
--   Prove2Me coordinate derivative definition https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d, inspected 26 October 2026; Mathlib Fréchet derivatives https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Mul.html.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Mathlib.Analysis.Calculus.FDeriv.Mul

theorem ItoLemma.fin_two_coordinate_product_gradient_components (z : Fin 2 → ℝ) :
    LevyStochCalc.coordDeriv
      (fun x : Fin 2 → ℝ =>
        x 0 • (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        x 1 • (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (0 : Fin 2) z = z 1 ∧
    LevyStochCalc.coordDeriv
      (fun x : Fin 2 → ℝ =>
        x 0 • (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        x 1 • (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (1 : Fin 2) z = z 0 := by sorry
