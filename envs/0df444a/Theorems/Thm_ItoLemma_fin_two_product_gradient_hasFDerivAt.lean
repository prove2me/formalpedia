-- Prove2me | Theorems.Thm_ItoLemma_fin_two_product_gradient_hasFDerivAt
-- name    : ItoLemma.fin_two_product_gradient_hasFDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:47:29.021307+00:00
-- url     : https://prove2.me/theorems/8d1fda7f-b48f-4c99-971e-1f5d313284c7
-- title:
--   Constant Mixed Hessian of the Two-Coordinate Product
-- statement:
--   The Fréchet derivative of the gradient map of f(x)=x₀x₁ is the constant continuous linear operator H(v)=v₀·proj₁+v₁·proj₀. This operator is the symmetric mixed Hessian, with zero diagonal entries and unit off-diagonal entries.
-- source:
--   Pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, ContinuousLinearMap.smulRight and ContinuousLinearMap.hasFDerivAt source headers verified 26 October 2026; official documentation https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Linear.html.

import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

theorem ItoLemma.fin_two_product_gradient_hasFDerivAt (z : Fin 2 → ℝ) :
    HasFDerivAt
      (fun x : Fin 2 → ℝ =>
        x 0 • (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        x 1 • (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))
      (((ContinuousLinearMap.proj (0 : Fin 2) :
            (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)) +
        ((ContinuousLinearMap.proj (1 : Fin 2) :
            (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ))) z := by sorry
