-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenSubexponentialAffineEnvelope
-- name    : Kyprianou.Ch07.kestenSubexponentialAffineEnvelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T22:37:07.787726+00:00
-- url     : https://prove2.me/theorems/7867e96e-5c44-4c51-afbf-d5fbd62e5b43
-- title:
--   Lemma 7.14 technical heart: uniform affine envelope for subexponential convolution tails
-- statement:
--   Given the full source premises of Kesten’s lemma, namely a probability distribution with positive tail at every positive x and asymptotic n-fold convolution upper-tail ratio n for every fixed n>=2, prove that, for every epsilon>0, there exist finite nonnegative constants A,B and a single real-valued envelope sequence bounding all convolution tail ratios uniformly in x and obeying xi(0)<=B and xi(n+1)<=A+(1+epsilon)xi(n). This encodes the analytic one-big-jump splitting step needed before the already proved geometric-recursion argument can establish the full Kesten bound.
-- source:
--   Kyprianou (2006), Lemma 7.14 proof, printed pp.201–202, original PDF pp.210–211. Source-faithful nontrivial analytic reduction of original milestone 6402f145-487e-4df9-8af6-1ffe5610a800.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenSubexponentialAffineEnvelope
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConvolutionAsymptotics : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ A B : Real, 0 ≤ A ∧ 0 ≤ B ∧
        ∃ xi : Nat → Real,
          xi 0 ≤ B ∧
          (∀ n : Nat, xi (n + 1) ≤ A + (1 + epsilon) * xi n) ∧
          ∀ n : Nat, 1 ≤ n →
            ∀ x : Real, 0 < x →
              ((convolutionPower G n) (Set.Ioi x)).toReal /
                (G (Set.Ioi x)).toReal ≤ xi n := by
  sorry
