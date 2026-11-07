-- Prove2me | Theorems.Thm_OAI_QuadraticInitialBound_quadratic_initial_finite_bound
-- name    : OAI.QuadraticInitialBound.quadratic_initial_finite_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:01.064488+00:00
-- url     : https://prove2.me/theorems/72a19440-eaed-459e-a260-8a41ee23a5ed
-- title:
--   Quadratic Initial Bound: quadratic initial finite bound
-- statement:
--   The Quadratic Initial Bound construction uses the quadratic initial finite bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean#L426-L459
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/InitialBound.lean#L426-L459

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
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
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem OAI.QuadraticInitialBound.quadratic_initial_finite_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * quadraticRow P hg (support n) z‖ ^ 2) ≤
      (diagonalControl sieveCutoff * M + pvControl sieveCutoff * N * C.card) *
        ∑ n ∈ C, ‖a n‖ ^ 2 := by sorry
