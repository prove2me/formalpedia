-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_actual_principal_difference
-- name    : OAI.CanonicalQuadraticSieve.HasSieveExponent.actual_principal_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:34:01.800452+00:00
-- url     : https://prove2.me/theorems/68c650a1-a6f4-4b36-be1d-bb2a34e0a664
-- title:
--   Has Sieve Exponent: actual principal difference
-- statement:
--   The Has Sieve Exponent construction uses the actual principal difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/MaskedPrincipalBounds.lean#L256-L290
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/MaskedPrincipalBounds.lean#L256-L290

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspIntegration
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MaskedPrincipalBounds
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
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator

theorem OAI.CanonicalQuadraticSieve.HasSieveExponent.actual_principal_difference {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (cols : n → Ideal O) (_hinj : Function.Injective cols)
      (M N K : ℝ), 1 ≤ M → 1 ≤ N → 1 ≤ K →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      (∀ j k, columnRay (cols j) = columnRay (cols k)) →
      ∀ (a : n → ℂ) (G : Ideal O), Squarefree G →
      (∀ P ∈ fixedBadPrimes, P ∣ G) → ∀ (ε : ℝ) (hε : 0 < ε),
      ‖(Real.sqrt M : ℂ) * actualPrincipalDifference cols a G K‖ ≤
        ((idealDivisors G).card : ℝ)^2 * (supportConstant ε hε * N^ε) *
          C * (K*N)^deltaLoss * (Real.sqrt (M/K)*N + Real.sqrt M*K^(α-1/2)) *
          ∑ j, ‖a j‖^2 := by sorry
