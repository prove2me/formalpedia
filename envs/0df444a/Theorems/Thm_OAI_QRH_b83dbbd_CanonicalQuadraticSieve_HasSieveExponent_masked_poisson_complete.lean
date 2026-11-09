-- Prove2me | Theorems.Thm_OAI_QRH_b83dbbd_CanonicalQuadraticSieve_HasSieveExponent_masked_poisson_complete
-- name    : OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.masked_poisson_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T04:01:01.296212+00:00
-- url     : https://prove2.me/theorems/2b6d87a5-0227-4e1a-a394-afaa4a20da29
-- title:
--   Has Sieve Exponent: masked poisson complete
-- statement:
--   The Has Sieve Exponent construction uses the masked poisson complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean#L333-L381
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean#L333-L381

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ScaleCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
set_option autoImplicit false
open OAI
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

theorem OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.masked_poisson_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (ε : ℝ) (hε : 0<ε)
        (G : Ideal OAI.CanonicalQuadraticSieve.O), Squarefree G → (∀P∈fixedBadPrimes,P∣G) →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 1≤M → 4≤T →
      ∀ (cols : n → Ideal OAI.CanonicalQuadraticSieve.O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) → (∀j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W := by sorry

alias «OAI».«CanonicalQuadraticSieve».«HasSieveExponent».«masked_poisson_complete» := OAI.QRH_b83dbbd.CanonicalQuadraticSieve.HasSieveExponent.masked_poisson_complete
