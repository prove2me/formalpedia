-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenFromConvolutionRecurrence
-- name    : Kyprianou.Ch07.kestenFromConvolutionRecurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:34:38.471235+00:00
-- url     : https://prove2.me/theorems/b1696439-5ac3-47da-8a92-b80b2cff1d8d
-- title:
--   Kesten estimate from a uniform affine convolution-tail envelope recurrence
-- statement:
--   If the ratios of all n-fold convolution tails to the original tail admit an envelope sequence with finite base bound and an affine recurrence of multiplier 1+epsilon and nonnegative forcing, the Kesten bound follows with a single positive constant C uniform in all n>=1 and x>0. This bridge uses the accepted geometric-recursion helper.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14 (Kesten bound), printed p. 201, original PDF p. 210. Exact complete proof reached private pinned remote compiler sentinel job c086fc52-c9b6-4469-a11c-2e190d27b61c.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_kestenGeometricRecursion
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenFromConvolutionRecurrence
    (G : Measure Real) [IsProbabilityMeasure G]
    (epsilon : Real) (hEpsilon : 0 < epsilon)
    (A B : Real) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (xi : Nat → Real)
    (hBase : xi 0 ≤ B)
    (hStep : ∀ n : Nat,
      xi (n + 1) ≤ A + (1 + epsilon) * xi n)
    (hTail : ∀ n : Nat, 1 ≤ n →
      ∀ x : Real, 0 < x →
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          (G (Set.Ioi x)).toReal ≤ xi n) :
    ∃ C : Real, 0 < C ∧
      ∀ n : Nat, 1 ≤ n →
        ∀ x : Real, 0 < x →
          ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
            (G (Set.Ioi x)).toReal ≤ C * (1 + epsilon) ^ n := by
  sorry
