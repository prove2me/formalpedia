-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenTwofoldEventualTailBound
-- name    : Kyprianou.Ch07.kestenTwofoldEventualTailBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:46:06.676139+00:00
-- url     : https://prove2.me/theorems/04aff3bc-e5c9-4255-a6b9-758edcc929c6
-- title:
--   Kesten: twofold convolution tail ratio eventually below 2+epsilon
-- statement:
--   For every epsilon>0, a probability distribution G with strictly positive upper tails and the source twofold convolution asymptotic has a positive real threshold T such that, for all x>=T, the ratio of the twofold convolution upper tail to the original upper tail is strictly less than 2+epsilon. This is the actual source-based asymptotic input controlling the coefficient of the affine recurrence in Kesten’s lemma.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed pp.201–202, original PDF pp.210–211, including the bound involving the twofold tail. Exact source remote kernel elaboration job 495f0898-ee48-4577-b889-71df3a9af69a.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenTwofoldEventualTailBound
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConvTwo : Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G 2) (Set.Ioi x)).toReal /
          ((2 : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real)))
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    ∃ T : Real, 0 < T ∧
      ∀ x : Real, T ≤ x →
        ((Kyprianou.Ch07.convolutionPower G 2) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal < 2 + epsilon := by
  sorry
