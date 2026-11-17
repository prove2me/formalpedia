-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenBoundSubexponentialConvolution
-- name    : Kyprianou.Ch07.kestenBoundSubexponentialConvolution
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:49:26.531762+00:00
-- url     : https://prove2.me/theorems/6402f145-487e-4df9-8af6-1ffe5610a800
-- title:
--   Lemma 7.14: Kesten bound for subexponential convolution tails
-- statement:
--   Lemma 7.14 (Kesten's uniform bound). Let G be the distribution of any random variable, with strictly positive upper tail for every positive threshold, and suppose its convolution powers obey G^{*n}(x,∞)∼n G(x,∞) for all integers n≥2. For every ε>0 there is C(ε)>0 such that G^{*n}(x,∞)/G(x,∞)≤C(ε)(1+ε)^n for all integers n≥1 and x>0.
-- source:
--   Kyprianou (2006), Lemma 7.14, printed p.201, Windows Ky.pdf landscape sheet 106 (original single-page PDF p.210).

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Lemma 7.14: a uniform exponential-in-n bound for convolution
tails of any probability distribution obeying (7.22). -/
theorem kestenBoundSubexponentialConvolution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConvolutionAsymptotics : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ C : Real, 0 < C ∧
        ∀ n : Nat, 1 ≤ n →
          ∀ x : Real, 0 < x →
            ((convolutionPower G n) (Set.Ioi x)).toReal /
              (G (Set.Ioi x)).toReal ≤ C * (1 + epsilon) ^ n := by
  sorry

end Kyprianou.Ch07
