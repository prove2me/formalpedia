-- Prove2me | Theorems.Thm_HasSmoothJordanOuterApproximation_homothety
-- name    : HasSmoothJordanOuterApproximation.homothety
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:58:37.391523+00:00
-- url     : https://prove2.me/theorems/f89be689-5c3d-48f9-a020-8198487ddf53
-- title:
--   Has Smooth Jordan Outer Approximation: homothety
-- statement:
--   Smooth Jordan outer approximation is preserved by a nontrivial real
--   homothety about any center.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L108-L123
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L108-L123

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem HasSmoothJordanOuterApproximation.homothety
    {K : Set ℂ} (hK : HasSmoothJordanOuterApproximation K)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0) :
    HasSmoothJordanOuterApproximation (AffineMap.homothety c r '' K) := by sorry
