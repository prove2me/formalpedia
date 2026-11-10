-- Prove2me | Theorems.Thm_OAI_CompletedGauss_integrated_product_quadratic
-- name    : OAI.CompletedGauss.integrated_product_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:53:24.406178+00:00
-- url     : https://prove2.me/theorems/ef5ac262-02f8-4965-9831-00f73e4f07be
-- title:
--   Completed Gauss: integrated product quadratic
-- statement:
--   The Completed Gauss construction uses the integrated product quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/DirichletForm.lean#L297-L336
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/DirichletForm.lean#L297-L336

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups
open OAI.CompletedGauss
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open CanonicalQuadraticSieve ActualEisensteinCubic

theorem OAI.CompletedGauss.integrated_product_quadratic (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : ℝ→Ideal O→Ideal O→ℂ,
      (∀n b,Continuous (fun t => β t n b)) →
      (∀t,∀n∈S,∀b∈T,‖β t n b‖≤lengthScale) →
    ∀rowPhase : idealRange K→ℝ→ℂ,(∀k,Continuous (rowPhase k)) → (∀k t,‖rowPhase k t‖≤1) →
    ∀b : 𝓢(ℝ,ℂ),
      (∑k : idealRange K,‖∫t : ℝ,b t*(rowPhase k t*
        ∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β t n v)‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2*(∫t : ℝ,‖b t‖)^2 := by sorry
