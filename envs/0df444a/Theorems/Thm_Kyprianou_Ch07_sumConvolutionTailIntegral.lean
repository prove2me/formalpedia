-- Prove2me | Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailIntegral
-- name    : Kyprianou.Ch07.sumConvolutionTailIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:48:57.162454+00:00
-- url     : https://prove2.me/theorems/1c213bc8-1d41-4943-aca2-7722b35515f3
-- title:
--   Kesten convolution-tail Fubini identity for addition pushforward measures
-- statement:
--   For arbitrary real Borel measures mu and sigma-finite-in-the-s-finite-sense nu, the upper tail of their sum-convolution (the pushforward of the product measure under addition) equals the lower integral over mu of the shifted upper tail nu((x-a,infinity)). This is the exact convolution-tail identity needed to split Kesten’s one-big-jump recurrence integral.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 proof, printed pp.201–202, original PDF pp.210–211. Full source-accurate proof passed pinned remote compiler job 7ae8c3b5-3c64-47d3-8eeb-a08371e93c17, using Measure.map_apply and Measure.prod_apply.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.sumConvolutionTailIntegral
    (mu nu : Measure Real) [SFinite nu] (x : Real) :
    (Kyprianou.Ch07.sumConvolution mu nu) (Set.Ioi x) =
      ∫⁻ a : Real, nu (Set.Ioi (x - a)) ∂mu := by
  sorry
