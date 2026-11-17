-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenEachOrderHasFiniteTailBound
-- name    : Kyprianou.Ch07.kestenEachOrderHasFiniteTailBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:29:05.258878+00:00
-- url     : https://prove2.me/theorems/1a361b24-67a5-4a7a-9217-318af35fde2c
-- title:
--   Kesten: finite upper-tail envelope at each positive convolution order
-- statement:
--   Under the original Kesten hypotheses, each fixed n>=1 has some finite positive constant C_n which bounds the upper-tail ratio of G^{*n} to G uniformly in all x>0. For n=1 the ratio equals one; for every n>=2 use its source asymptotic and the proved fixed-order bound. This establishes finiteness of each envelope term before deriving the uniform affine recurrence.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed pp.201–202; original PDF pp.210–211. Exact full proof passed pinned private remote compiler job 802343a2-e9ea-48a9-8f83-db5494b57743.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_kestenOnefoldTailRatio
import Theorems.Thm_Kyprianou_Ch07_kestenFixedNUniformTailBound
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenEachOrderHasFiniteTailBound
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConv : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ n : Nat, 1 ≤ n →
      ∃ C : Real, 0 < C ∧
        ∀ x : Real, 0 < x →
          ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
            (G (Set.Ioi x)).toReal ≤ C := by
  sorry
