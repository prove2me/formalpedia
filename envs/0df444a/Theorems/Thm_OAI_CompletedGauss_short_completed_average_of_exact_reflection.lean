-- Prove2me | Theorems.Thm_OAI_CompletedGauss_short_completed_average_of_exact_reflection
-- name    : OAI.CompletedGauss.short_completed_average_of_exact_reflection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:36:28.526954+00:00
-- url     : https://prove2.me/theorems/8cdd46fd-adf7-4d01-8c56-2ca9227cda94
-- title:
--   Completed Gauss: short completed average of exact reflection
-- statement:
--   The Completed Gauss construction uses the short completed average of exact reflection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CompletedDyadicRows.lean#L314-L379
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CompletedDyadicRows.lean#L314-L379

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve

theorem OAI.CompletedGauss.short_completed_average_of_exact_reflection
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal O→O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) W (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) W X (Z^(1/1000:ℝ))‖^2)/F≤
        C*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by sorry
