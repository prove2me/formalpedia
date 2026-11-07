-- Prove2me | Theorems.Thm_OAI_SquarefreeDivisorBound_first_element_energy_small_power
-- name    : OAI.SquarefreeDivisorBound.first_element_energy_small_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:14:01.125128+00:00
-- url     : https://prove2.me/theorems/21c65b95-8620-4bbd-9ae5-39b7fe4e16bb
-- title:
--   Squarefree Divisor Bound: first element energy small power
-- statement:
--   The Squarefree Divisor Bound construction uses the first element energy small power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/SquarefreeDivisors.lean#L192-L214
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/SquarefreeDivisors.lean#L192-L214

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
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
open OAI.SquarefreeDivisorBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum
open DescentWeightedCauchy

theorem OAI.SquarefreeDivisorBound.first_element_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × O)) (t : Finset O)
      (e : O) (w : Ideal O × O → ℂ) (P : O → ℂ) (B Y : ℝ),
      0 ≤ B → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, firstElementRowMap e x ∈ t) → (∀ y ∈ t, y ≠ 0) →
      (∀ y ∈ t, (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (firstElementRowMap e x)‖ ^ 2) ≤
        B * C * Y ^ ε * ∑ y ∈ t, ‖P y‖ ^ 2 := by sorry
