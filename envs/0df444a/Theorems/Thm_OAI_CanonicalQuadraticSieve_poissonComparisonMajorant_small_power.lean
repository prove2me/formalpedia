-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_poissonComparisonMajorant_small_power
-- name    : OAI.CanonicalQuadraticSieve.poissonComparisonMajorant_small_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T06:19:27.452195+00:00
-- url     : https://prove2.me/theorems/b69305f0-ac2b-4b77-93d4-08a5253bb6e6
-- title:
--   Canonical Quadratic Sieve: poisson Comparison Majorant small power
-- statement:
--   The Canonical Quadratic Sieve construction uses the poisson Comparison Majorant small power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/SelectedExponents.lean#L78-L114
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/SelectedExponents.lean#L78-L114

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
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
open ActualEisensteinCubic IdealCoprimeSieveOperator

theorem OAI.CanonicalQuadraticSieve.poissonComparisonMajorant_small_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (ρ : ℝ) (hρ : 0<ρ) :
    ∃ (η : ℝ) (hη : 0<η), η≤1 ∧ 259*η≤ρ ∧
    ∃ (l A : ℕ), 4≤η*l ∧ 4≤η*A ∧
      ∀ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
        0≤CD → 0≤CS → 0≤CT → 0≤CP →
      ∀ (B C1 : ℝ), 1≤B → 1≤C1 → ∀ (W : 𝓢(ℝ,ℂ)),
      ∃ Cfinal : ℝ, 0<Cfinal ∧
        ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
          1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
          1≤selectedPoissonK C M X η →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
          (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
          (fun _ : Unit => (1:ℂ)) W ≤
          Cfinal*(M*X)^ρ*poissonShape M X α := by sorry
