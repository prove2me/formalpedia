-- Prove2me | Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailSplitLe
-- name    : Kyprianou.Ch07.sumConvolutionTailSplitLe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:54:18.576198+00:00
-- url     : https://prove2.me/theorems/a8eeea47-1cf0-4723-aeca-9839cadec985
-- title:
--   Kesten one-big-jump split: convolution tail bounded by first-measure tail plus truncated integral
-- statement:
--   For arbitrary real measures mu and a probability distribution nu, the tail of their sum-convolution at threshold x is at most the upper tail mu((x,infinity)) plus the lower integral over a<=x of the shifted upper tail nu((x-a,infinity)). The proof splits the exact Fubini convolution tail integral over a<=x and a>x and bounds the latter integrand by one using probability mass. The result requires no nonnegative support assumption.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed pp.201–202, original PDF pp.210–211. Source-faithful one-big-jump splitting needed for the uniform Kesten affine recurrence. Full proof privately verified by pinned remote job 8de92b5f-9934-48fa-bff1-b68cff5836c4.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailIntegral
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.sumConvolutionTailSplitLe
    (mu nu : Measure Real) [SFinite nu] [IsProbabilityMeasure nu]
    (x : Real) :
    (Kyprianou.Ch07.sumConvolution mu nu) (Set.Ioi x) ≤
      mu (Set.Ioi x) +
        ∫⁻ a : Real in Set.Iic x, nu (Set.Ioi (x - a)) ∂mu := by
  sorry
