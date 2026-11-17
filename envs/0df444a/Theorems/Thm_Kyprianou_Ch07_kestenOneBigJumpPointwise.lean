-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenOneBigJumpPointwise
-- name    : Kyprianou.Ch07.kestenOneBigJumpPointwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T23:39:05.756806+00:00
-- url     : https://prove2.me/theorems/c1b31213-55ec-47b3-b586-5d92fc6a2cc8
-- title:
--   Kesten analytic heart: pointwise one-big-jump estimate uniform in n and threshold
-- statement:
--   Under the source subexponential hypotheses, for every epsilon>0 there exists a constant A>=1 such that for all n>=1 and x>0 the (n+1)-fold convolution upper-tail ratio at x is bounded by A+(1+epsilon)ξ_n, where ξ_n is the exact supremum of nth convolution-tail ratios. This is the quantified one-big-jump integral-splitting inequality from the proof of Lemma 7.14. It must be proved using the convolution-tail integral formula, source twofold asymptotics, and the large/small threshold decomposition.
-- source:
--   Kyprianou (2006), Lemma 7.14 proof, printed pp.201–202, original PDF pp.210–211, particularly the displayed ξ_(n+1) estimate based on 1−G^{*(n+1)}=1−G*(1−G^{*n}).

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenOneBigJumpPointwise
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
        ∀ x : Real, 0 < x →
          ((Kyprianou.Ch07.convolutionPower G (n + 1))
            (Set.Ioi x)).toReal / (G (Set.Ioi x)).toReal ≤
              A + (1 + epsilon) * Kyprianou.Ch07.kestenSupEnvelope G n := by
  sorry
