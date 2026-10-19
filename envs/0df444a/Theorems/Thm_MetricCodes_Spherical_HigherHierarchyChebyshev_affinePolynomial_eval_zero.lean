-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_affinePolynomial_eval_zero
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.affinePolynomial_eval_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:31.984834+00:00
-- url     : https://prove2.me/theorems/11524c28-7801-4b69-930a-483320b807a5
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.affinePolynomial_eval_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.affinePolynomial_eval_zero {R : ℝ} (hR : 0 < R)
    (N j : ℕ) :
    (affinePolynomial R).eval (zero R N j) =
      Real.cos (zeroAngle N j) := by sorry
