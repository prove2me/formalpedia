-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceTonelliSwap
-- name    : Kyprianou.Ch01.stableAlphaOneLaplaceTonelliSwap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:24:44.197183+00:00
-- url     : https://prove2.me/theorems/616a216f-2cbd-4078-a157-c2553de1bc4e
-- title:
--   Tonelli integral order exchange for the stable index-one positive Laplace cosine kernel
-- statement:
--   Interchanging the order of two positive-half-line extended nonnegative Lebesgue integrals of the measurable kernel a exp(−a x)(1−cos x) leaves the result unchanged. Because the kernel is nonnegative for a,x>0, the Tonelli equality needs no circular absolute-integrability assumption. This is the core safe Fubini step that connects the stable alpha-one cosine integral with the rational 1/(1+a²) kernel.
-- source:
--   Kyprianou (2006), Chapter 1, α=1 stable Lévy exponent; Tonelli applied to the positive Laplace representation.

import Mathlib
open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLaplaceTonelliSwap :
    (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ a in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
    ∫⁻ a in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x)) := by
  sorry
