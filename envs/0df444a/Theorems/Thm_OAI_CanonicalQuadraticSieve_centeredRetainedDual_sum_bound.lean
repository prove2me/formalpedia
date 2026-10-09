-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_centeredRetainedDual_sum_bound
-- name    : OAI.CanonicalQuadraticSieve.centeredRetainedDual_sum_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T22:26:01.761825+00:00
-- url     : https://prove2.me/theorems/5af4344c-6e71-4cd5-b0d2-d94a3d3c3e84
-- title:
--   Sum over divisors of the centered retained dual terms
-- statement:
--   For every $l\in\mathbb N$ there are a finite set $s\subseteq\mathbb N\times\mathbb N$ and $C>0$ such that: for every finite index type $n$, every real $\alpha\ge1/2$ with `HasSieveExponent α` (witness `hexp`), every $\delta_{\mathrm{loss}}>0$ and $\varepsilon>0$, every nonzero ideal $G$ of $\mathcal O$ (`ActualEisensteinCubic.O`), all reals $K,N\ge1$, $M>0$, $T\ge4$, every injective `cols : n → Ideal O` whose members are `Admissible`, have absolute norm in $[N/2,N]$ and share one `columnRay`, every $a:n\to\mathbb C$ and every Schwartz function $W$,
--   $$\sum_{q\in\texttt{idealDivisors}\,G}\|\texttt{centeredRetainedDual}\ W\,\mathrm{cols}\,a\,M\,K\,q\|\le|\texttt{idealDivisors}\,G|\cdot(\texttt{columnDyadicLength}\,K+1)\cdot\texttt{retainedDualMajorant}\ s\,C\,l\,\texttt{hexp}\,\delta_{\mathrm{loss}}\,\varepsilon\,(2K)\,N\,M\,1\,T\,a\,(\texttt{quadraticTransformedSquareProfile}\,W).$$
--
--   Lean: `OAI.CanonicalQuadraticSieve.centeredRetainedDual_sum_bound` in `lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B007

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

namespace CanonicalQuadraticSieve

section

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

theorem centeredRetainedDual_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        (∑q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) ≤
          (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
            retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
  sorry

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

end CanonicalQuadraticSieve

open scoped BigOperators Classical

end

end OAI
end
