-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_originalPairLow_squarefree_tsum
-- name    : OAI.CanonicalQuadraticSieve.originalPairLow_squarefree_tsum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T00:19:42.639024+00:00
-- url     : https://prove2.me/theorems/8ecc7ac0-2867-4d29-99ca-0a90c124c36e
-- title:
--   Squarefree decomposition of the low original pair sum
-- statement:
--   For admissible ideals $I,J$ of $\mathcal O$ (`ActualEisensteinCubic.O`), every Schwartz function $W:\mathbb R\to\mathbb C$ and reals $M>0$ and $K$,
--   $$\sum_{L}\texttt{originalPairLow}\ I\ J\ W\ M\ K\ L=\sum_{B\ \text{admissible},\ \mathrm N(B)\le K}\texttt{quadraticRow}\,I\,(\pi_B)\,\texttt{quadraticRow}\,J\,(\pi_B)\sum_{A\ \text{supported}}\texttt{idealZeroMask}\,I\,(\pi_A)\,\texttt{idealZeroMask}\,J\,(\pi_A)\,W\Big(\frac{\mathrm N(A)^2\,\mathrm N(B)}{M}\Big),$$
--   where the left sum runs over all ideals $L$ of $\mathcal O$, $\pi_B$ is `primaryGenerator B`, $\mathrm N$ is the absolute norm, and all sums are `tsum`s (the terms with $\mathrm N(B)>K$ are $0$).
--
--   Lean: `OAI.CanonicalQuadraticSieve.originalPairLow_squarefree_tsum` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B006

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

theorem originalPairLow_squarefree_tsum
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑' B : {B : Ideal O // Admissible B},
        if (Ideal.absNorm B.val : ℝ) ≤ K then
          (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
            ∑' A : {A : Ideal O // Supported A},
              (idealZeroMask I (primaryGenerator A.val) * idealZeroMask J (primaryGenerator A.val)) *
                W (((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) / M)
        else 0 := by
  sorry

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

end CanonicalQuadraticSieve

end

end OAI
end
