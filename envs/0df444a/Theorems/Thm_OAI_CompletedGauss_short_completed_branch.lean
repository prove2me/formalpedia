-- Prove2me | Theorems.Thm_OAI_CompletedGauss_short_completed_branch
-- name    : OAI.CompletedGauss.short_completed_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T08:21:29.830577+00:00
-- url     : https://prove2.me/theorems/f32285cb-5594-4d12-90a1-833557dcef03
-- title:
--   Completed Gauss: short completed branch
-- statement:
--   The Completed Gauss construction uses the short completed branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean#L328-L347
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/ProductColumns.lean#L328-L347

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
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
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve

theorem OAI.CompletedGauss.short_completed_branch {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (W : ℝ → ℂ) (Z K R X F A : ℝ)
    (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hA : 0≤A)
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ)))
    (hcompleted : ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
      (∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*R*F*(Ideal.absNorm H:ℝ)^3/X)) :
    (∑k,‖shortCompletedSum (Ψ k) W X (Z^(1/1000:ℝ))‖^2)≤
      (2*A*K)*(256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2 := by sorry
