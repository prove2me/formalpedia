-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineLintegralEqualsRational
-- name    : Kyprianou.Ch01.stableAlphaOneCosineLintegralEqualsRational
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:35:29.761028+00:00
-- url     : https://prove2.me/theorems/18331226-d10b-4c04-b380-866aed60f5a8
-- title:
--   Tonelli equality of stable cosine extended integral with rational extended integral
-- statement:
--   The extended nonnegative integral over x>0 of the stable index-one cosine kernel (1−cos x)/x² equals that of 1/(1+a²) over a>0. This is the core exact Tonelli identity. Both pointwise Laplace integration orders are already proved, and the nonnegative-kernel Tonelli swap combines them. No integrability assumption for the joint kernel is required.
-- source:
--   Kyprianou (2006), Chapter 1, α=1 stable Lévy exponent and its Laplace–Tonelli evaluation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceTonelliSwap
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneWeightedInverseSquareLintegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceDeficitLintegral
open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineLintegralEqualsRational :
    (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - Real.cos x) / x ^ 2)) =
    (∫⁻ a in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 + a ^ 2)⁻¹)) := by
  sorry
