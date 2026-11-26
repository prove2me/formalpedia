-- Prove2me | Theorems.Thm_Kyprianou_Ch05_renewalKernelSumInterchange
-- name    : Kyprianou.Ch05.renewalKernelSumInterchange
-- status  : Open
-- author  : @DAGA
-- created : 2026-11-26T03:07:06.30187+00:00
-- url     : https://prove2.me/theorems/65725ea4-9e02-5c84-90e8-1334d22b0da1
-- title:
--   Lemma 5.5 step: epoch sum equals the renewal-measure kernel
-- statement:
--   The renewal measure $U = \sum_{n=0}^{\infty} F^{*n}$ is by definition the countable sum of the convolution powers of $F$. For any level $x$ and any sets $A, B \subseteq \mathbb{R}$, the sum over $n$ of the double lower integrals $\int_{v \in [0,x]} \int_{z > x-v} \mathbf{1}\{z - (x-v) \in A,\ x - v \in B\} \, dF(z) \, dF^{*n}(v)$ equals the single double integral against $U$, which is the joint kernel $K_{U,F}(x, A, B)$. This is the interchange of a countable sum of measures with a lower Lebesgue integral; no measurability of $A$ or $B$ is needed because lower integrals and the indicator are defined for arbitrary sets.
-- source:
--   Kyprianou (2006), first edition, Lemma 5.5, printed pp.116-117, equation (5.5).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05
open Classical in
theorem renewalKernelSumInterchange
    (F : Measure Real) (x : Real) (A B : Set Real) :
    (∑' n : Nat, ∫⁻ v in Set.Icc (0 : Real) x,
      (∫⁻ z in Set.Ioi (x - v),
        (if z - (x - v) ∈ A ∧ x - v ∈ B then (1 : ENNReal) else 0) ∂F)
      ∂(renewalConvolutionPower F n)) =
    renewalJointKernel (renewalMeasure F) F x A B := by
  sorry
end Kyprianou.Ch05
