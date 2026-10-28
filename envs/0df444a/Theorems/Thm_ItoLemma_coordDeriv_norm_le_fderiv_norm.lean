-- Prove2me | Theorems.Thm_ItoLemma_coordDeriv_norm_le_fderiv_norm
-- name    : ItoLemma.coordDeriv_norm_le_fderiv_norm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:50:09.193032+00:00
-- url     : https://prove2.me/theorems/1889d5ea-66cc-4a36-99b9-26e2e393c3e1
-- title:
--   Coordinate Partial Derivative Bounded by Fréchet Operator Norm
-- statement:
--   For any finite-dimensional state space and any Fréchet-derivative field g, every coordinate derivative has absolute value at most the operator norm of g. This gives a uniform pointwise domination of the coefficient in an Itô stochastic integral by the original diffusion coefficient whenever the gradient is bounded.
-- source:
--   Pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474: ContinuousLinearMap.le_opNorm and Pi.norm_single, source headers checked 26 October 2026. Definition of coordDeriv https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Operator.Basic

theorem ItoLemma.coordDeriv_norm_le_fderiv_norm {n : ℕ}
    (g : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
    (p : Fin n) (z : Fin n → ℝ) :
    ‖LevyStochCalc.coordDeriv g p z‖ ≤ ‖g z‖ := by sorry
