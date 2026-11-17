-- Prove2me | Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailProductLower
-- name    : Kyprianou.Ch07.sumConvolutionTailProductLower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:44:39.033367+00:00
-- url     : https://prove2.me/theorems/8526375a-bb54-48a7-9617-d5fb9b8497ab
-- title:
--   Kesten: product of shifted upper tails bounds the twofold convolution tail below
-- statement:
--   For a real probability measure G and real x,T, the product G((x−T,infinity))*G((T,infinity)) is at most the twofold sum-convolution upper-tail probability at x. This follows because the rectangle of pairs satisfying each upper-tail condition is included in the event that their sum exceeds x. It supplies quantitative shifted-tail bounds from the fixed-order convolution estimate.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 Kesten bound proof, printed pp.201–202, original PDF pp.210–211; pinned private remote compiler proof ae91f536-14ad-4c65-a258-e29c0ef46135.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.sumConvolutionTailProductLower
    (G : Measure Real) [IsProbabilityMeasure G] (x T : Real) :
    G (Set.Ioi (x - T)) * G (Set.Ioi T) ≤
      (Kyprianou.Ch07.sumConvolution G G) (Set.Ioi x) := by
  sorry
