-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenSupEnvelopeAffineStep
-- name    : Kyprianou.Ch07.kestenSupEnvelopeAffineStep
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T23:35:31.810219+00:00
-- url     : https://prove2.me/theorems/e483bfae-6402-48af-a1b2-f8b44e12451c
-- title:
--   Kesten analytic core: uniform-in-n one-big-jump affine recurrence for sup tail ratios
-- statement:
--   Under the complete original Kesten hypotheses, for each epsilon>0 there is a single constant A>=1 so that every n>=1 satisfies ξ_(n+1) <= A+(1+epsilon)ξ_n, where ξ_n is exactly the supremum over all x>0 of the n-fold convolution-tail ratio. The n=1 and finite ξ_n cases are already independently proved. This remainder requires the nontrivial source one-big-jump integral splitting and the twofold convolution asymptotic. No extra assumptions are introduced.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 proof, printed pp.201–202, original PDF pp.210–211, source bound (7.22) and ξ_(n+1) recurrence.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenSupEnvelopeAffineStep
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConv : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real)))
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    ∃ A : Real, 1 ≤ A ∧
      ∀ n : Nat, 1 ≤ n →
        Kyprianou.Ch07.kestenSupEnvelope G (n + 1) ≤
          A + (1 + epsilon) * Kyprianou.Ch07.kestenSupEnvelope G n := by
  sorry
