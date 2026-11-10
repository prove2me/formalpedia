-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_product_quadratic_norm_all
-- name    : OAI.CanonicalQuadraticSieve.product_quadratic_norm_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T08:24:08.520197+00:00
-- url     : https://prove2.me/theorems/c4fb787d-2f4d-4c33-b373-3b58f0968046
-- title:
--   Canonical Quadratic Sieve: product quadratic norm all
-- statement:
--   The Canonical Quadratic Sieve construction uses the product quadratic norm all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean#L77-L120
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/UniformTailBounds.lean#L77-L120

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem OAI.CanonicalQuadraticSieve.product_quadratic_norm_all :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K U B : ℝ,
      1≤K → 1≤U → 1≤B → ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖≤1) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
        C*(K*(U*B))^ε*(K+U*B)*(U*B) := by sorry
