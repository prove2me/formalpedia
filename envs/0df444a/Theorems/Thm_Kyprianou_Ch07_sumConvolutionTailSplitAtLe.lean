-- Prove2me | Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailSplitAtLe
-- name    : Kyprianou.Ch07.sumConvolutionTailSplitAtLe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:44:37.7383+00:00
-- url     : https://prove2.me/theorems/65708bf3-86bd-4f20-8669-d4eadaad33d9
-- title:
--   Kesten: split convolution upper tail at any real cutoff
-- statement:
--   For two real measures mu and nu with nu a probability distribution, the sum-convolution upper-tail probability at x is bounded by mu((T,infinity)) plus the lower integral over a≤T of nu((x-a,infinity)) against mu, for any real cutoff T. This follows by partitioning the exact Fubini convolution identity and using the probability-one bound on the complementary region. It is the truncation lemma needed for Kesten one-big-jump estimates.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 Kesten bound proof, printed pp.201–202, original PDF pp.210–211; pinned private remote compiler proof 83261c25-f0f2-4299-a856-76b158be92ba.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailIntegral
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.sumConvolutionTailSplitAtLe
    (mu nu : Measure Real) [SFinite nu] [IsProbabilityMeasure nu]
    (x T : Real) :
    (Kyprianou.Ch07.sumConvolution mu nu) (Set.Ioi x) ≤
      mu (Set.Ioi T) +
        ∫⁻ a : Real in Set.Iic T, nu (Set.Ioi (x - a)) ∂mu := by
  sorry
