-- Prove2me | Theorems.Thm_OAI_CompletedGauss_completed_reflected_branch_series
-- name    : OAI.CompletedGauss.completed_reflected_branch_series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T13:52:28.185623+00:00
-- url     : https://prove2.me/theorems/ca3ba06a-144b-4cfe-a976-bf1a0e7e8d32
-- title:
--   Completed Gauss: completed reflected branch series
-- statement:
--   The Completed Gauss construction uses the completed reflected branch series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/ReflectedDyadicSeries.lean#L556-L593
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/ReflectedDyadicSeries.lean#L556-L593

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CompletedGauss
open ActualEisensteinCubic
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

theorem OAI.CompletedGauss.completed_reflected_branch_series
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖reflectedBranchBlock P hg j e W K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock P hg j e W K Y ρ q S T η σ i k‖^2)
        ≤C*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by sorry
