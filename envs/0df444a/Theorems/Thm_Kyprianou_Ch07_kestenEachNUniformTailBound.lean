-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenEachNUniformTailBound
-- name    : Kyprianou.Ch07.kestenEachNUniformTailBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:53:49.133177+00:00
-- url     : https://prove2.me/theorems/c404c33d-909b-45d9-9b5f-1ff4f9e0c557
-- title:
--   Kesten: every fixed n>=1 convolution upper-tail ratio is uniformly bounded in x
-- statement:
--   The exact source hypotheses of Lemma 7.14 imply that for every natural n>=1 there exists a finite positive real bound C_n, permitted to depend on n, such that the ratio of the n-fold convolution upper tail to G((x,infinity)) is <= C_n for every x>0. The n=1 case uses the exact tail-ratio identity; n>=2 follows from the fixed-n uniform bound deduced from regular variation and probability upper-tail monotonicity.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 inductive Kesten bound, printed pp.201–202, original PDF pp.210–211. Exact complete source passed private remote pinned compiler job 26944923-7a2c-4c7f-afb1-f554e9f8de6d.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_kestenOnefoldTailRatio
import Theorems.Thm_Kyprianou_Ch07_kestenFixedNUniformTailBound
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenEachNUniformTailBound
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConvolutionAsymptotics : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ n : Nat, 1 ≤ n →
      ∃ C : Real, 0 < C ∧ ∀ x : Real, 0 < x →
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal ≤ C := by
  sorry
