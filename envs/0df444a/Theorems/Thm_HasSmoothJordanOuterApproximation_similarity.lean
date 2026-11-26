-- Prove2me | Theorems.Thm_HasSmoothJordanOuterApproximation_similarity
-- name    : HasSmoothJordanOuterApproximation.similarity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:25.574653+00:00
-- url     : https://prove2.me/theorems/adbb6ac2-31a6-516f-bd7a-1179e0225e2b
-- title:
--   Has Smooth Jordan Outer Approximation: similarity
-- statement:
--   Smooth Jordan outer approximation is preserved by every nonzero complex
--   similarity `z ↦ c + a * z`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L63-L94
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L63-L94

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem HasSmoothJordanOuterApproximation.similarity
    {K : Set ℂ} (hK : HasSmoothJordanOuterApproximation K)
    (c a : ℂ) (ha : a ≠ 0) :
    HasSmoothJordanOuterApproximation ((fun z => c + a * z) '' K) := by sorry
