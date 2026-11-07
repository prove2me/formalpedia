-- Prove2me | Theorems.Thm_OAI_SecondPassFiber_second_energy_pushforward
-- name    : OAI.SecondPassFiber.second_energy_pushforward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:17:32.003839+00:00
-- url     : https://prove2.me/theorems/bd564037-b5d3-4e98-ae0e-9654fdffd019
-- title:
--   Second Pass Fiber: second energy pushforward
-- statement:
--   The Second Pass Fiber construction uses the second energy pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/FiniteOperator.lean#L557-L592
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/FiniteOperator.lean#L557-L592

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
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
open OAI.SecondPassFiber
open scoped BigOperators Classical
open IdealMobiusDivisorSum ConcretePrimeRowBridge

theorem OAI.SecondPassFiber.second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (P : Ideal O × O → ℂ) (B H : ℝ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ H →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ H) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (newLabel x, newRow x)‖ ^ 2) ≤
        B * C * (H * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P z‖ ^ 2 := by sorry
