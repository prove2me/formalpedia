-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegral
-- name    : Kyprianou.Ch01.stableAlphaOneCosineIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:19:31.653833+00:00
-- url     : https://prove2.me/theorems/9b3f6d9b-dc0b-40dd-a005-81ff2750fb6c
-- title:
--   Exercise 1.4(ii): Cauchy/stable index-one cosine integral
-- statement:
--   Kyprianou Exercise 1.4(ii): the essential α=1 stable-law identity ∫₀∞(1−cos r)/r² dr=π/2, with its proper integrability assertion. This is a nontrivial Fourier-analytic component of the exceptional index-one stable exponent (1.8), not the full complex logarithmic phase formula. Draft awaiting remote elaboration.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(ii), printed p. 28.

import Mathlib
open MeasureTheory Filter Set Real
open scoped NNReal ENNReal Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineIntegral :
    IntegrableOn
      (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (1 - Real.cos r) / r ^ 2 ∂volume) = Real.pi / 2 := by
  sorry
