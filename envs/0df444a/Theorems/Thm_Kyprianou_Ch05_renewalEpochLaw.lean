-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalEpochLaw
-- name    : Kyprianou.Ch05.renewalEpochLaw
-- status  : Open
-- author  : @DAGA
-- created : 2026-11-26T03:06:09.267777+00:00
-- url     : https://prove2.me/theorems/d8914a4c-0e5b-41a8-914a-56eb893935ba
-- title:
--   Lemma 5.5 step: law of the nth renewal epoch is the nth convolution power
-- statement:
--   Let the spacings $Z_0, Z_1, \dots$ form a renewal epoch process with common law $F$: each $Z_n$ is measurable with pushforward law $F$, $F$ charges no negative values, $F(\{0\}) \neq 1$, and each new spacing $Z_n$ is independent of the accumulated epoch $S_n = Z_0 + \cdots + Z_{n-1}$ in the sense that $P(S_n \in A, Z_n \in B) = P(S_n \in A) F(B)$ for all measurable $A, B$. Then for every $n$, the law of the $n$-th renewal epoch $S_n$ under $P$ is the $n$-fold convolution power $F^{*n}$, with $F^{*0} = \delta_0$. This is proved by induction on $n$, the induction step being exactly the one-step independence applied to the convolution of measures.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
theorem renewalEpochLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Nat -> Omega -> Real) (F : Measure Real)
    (hRenewal : IsRenewalEpochProcess P Z F)
    (n : Nat) :
    Measure.map (renewalEpoch Z n) P = renewalConvolutionPower F n := by
  sorry
end Kyprianou.Ch05
