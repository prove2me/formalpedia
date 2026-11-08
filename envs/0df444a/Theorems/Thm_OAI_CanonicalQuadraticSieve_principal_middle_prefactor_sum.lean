-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_principal_middle_prefactor_sum
-- name    : OAI.CanonicalQuadraticSieve.principal_middle_prefactor_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:21:11.714891+00:00
-- url     : https://prove2.me/theorems/d546c70a-bb12-46b0-a1b2-49a268eb2cee
-- title:
--   Canonical Quadratic Sieve: principal middle prefactor sum
-- statement:
--   The Canonical Quadratic Sieve construction uses the principal middle prefactor sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/SpatialDerivatives.lean#L199-L218
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/SpatialDerivatives.lean#L199-L218

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalDifference
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SpatialDerivatives
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
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem OAI.CanonicalQuadraticSieve.principal_middle_prefactor_sum {m : Type*} [Fintype m]
    (S T : Finset (Ideal O)) (rows : m → Ideal O) (f : S → T → m → ℝ)
    (hf : ∀ D E i, 0 ≤ f D E i) (M B D₁ D₂ : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i) : ℝ))
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ)) (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ)) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) * f D E i) ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) * ∑ D : S, ∑ E : T, ∑ i, f D E i := by sorry
