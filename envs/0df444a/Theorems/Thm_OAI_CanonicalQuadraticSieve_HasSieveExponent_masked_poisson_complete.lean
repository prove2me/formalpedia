-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_masked_poisson_complete
-- name    : OAI.CanonicalQuadraticSieve.HasSieveExponent.masked_poisson_complete
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T22:42:52.449882+00:00
-- url     : https://prove2.me/theorems/bed9ee7b-15f4-481c-a46e-9c0676f511ec
-- title:
--   Masked Poisson difference is bounded by the Poisson comparison majorant
-- statement:
--   Let $\alpha\ge1/2$ be a real number for which `HasSieveExponent α` holds (with witness `hexp`), let $\delta_{\mathrm{loss}}>0$ and $l,A\in\mathbb N$. Then there are finite sets $s_D,s_S,s_T\subseteq\mathbb N\times\mathbb N$ and constants $C_D,C_S,C_T,C_P>0$ such that the following holds for every finite index type $n$ (with decidable equality), every $\varepsilon>0$, every squarefree ideal $G$ of $\mathcal O$ (the ring of integers of $\mathbb Q(\zeta_3)$, here `ActualEisensteinCubic.O`) divisible by every prime in `fixedBadPrimes`, all reals $K,N,M\ge1$ and $T\ge4$, every injective family of ideals `cols : n → Ideal O` with each `cols j` `Admissible`, of absolute norm in $[N/2,N]$, all with the same `columnRay` and each coprime to $G$, every $a:n\to\mathbb C$ and every Schwartz function $W$ with $W(0)=0$:
--   $$\big\|6\cdot\texttt{maskedPoissonDifference}\ G\ W\ \mathrm{cols}\ a\ M\ K\big\|\le\texttt{poissonComparisonMajorant}\ s_D\,s_S\,s_T\,C_D\,C_S\,C_T\,C_P\,l\,A\,\texttt{hexp}\,\delta_{\mathrm{loss}}\,\varepsilon\,G\,K\,N\,M\,T\,a\,W .$$
--
--   Lean: `OAI.CanonicalQuadraticSieve.HasSieveExponent.masked_poisson_complete` in `lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

theorem HasSieveExponent.masked_poisson_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G → (∀P∈fixedBadPrimes,P∣G) →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 1≤M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) → (∀j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W := by
  sorry

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

end CanonicalQuadraticSieve

open scoped BigOperators Classical

end

end OAI
end
