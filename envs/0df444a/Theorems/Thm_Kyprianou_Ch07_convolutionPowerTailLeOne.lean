-- Prove2me | Theorems.Thm_Kyprianou_Ch07_convolutionPowerTailLeOne
-- name    : Kyprianou.Ch07.convolutionPowerTailLeOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:41:30.030326+00:00
-- url     : https://prove2.me/theorems/7d95bbcc-9316-419d-948e-9eab89afe13b
-- title:
--   Kesten: every real convolution power upper tail has probability at most one
-- statement:
--   For any probability law on the reals, any natural n and real threshold x, the real value of the n-fold convolution distribution upper-tail probability is at most one. This uses the proved all-n probability normalisation and exact measure-to-real monotonicity.
-- source:
--   Kyprianou (2006), Lemma 7.14 proof, printed p.201, original PDF p.210. Exact full proof private-compiled under pinned Mathlib job 66785036-5052-414a-b016-75a29e582843.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.convolutionPowerTailLeOne
    (G : Measure Real) [IsProbabilityMeasure G]
    (n : Nat) (x : Real) :
    ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal ≤ 1 := by
  sorry
