-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalCubeInputFamilyEnergy_quantitative
-- name    : OAI.SecondPassArithmetic.globalCubeInputFamilyEnergy_quantitative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:55:35.0703+00:00
-- url     : https://prove2.me/theorems/74bdd4a9-4fea-4ecf-aabf-37676d1ad035
-- title:
--   Second Pass Arithmetic: global Cube Input Family Energy quantitative
-- statement:
--   The Second Pass Arithmetic construction uses the global Cube Input Family Energy quantitative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/InputEnergy.lean#L542-L620
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/InputEnergy.lean#L542-L620

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

theorem OAI.SecondPassArithmetic.globalCubeInputFamilyEnergy_quantitative
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀t,g t≠0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ),0≤C ∧ 0<Cd ∧ 0<Ct ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0 → |t|≤M+6+1) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2) (_hpr : ∀i,lambda^2∣p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (w : GlobalCubeBlock ι → ℝ) (Γ K ell B F H U : ℝ)
      (Ψ : O →* ℂ) (m : O) (T : GlobalCubeBlock ι → Finset O),
      0≤Γ → (∀b∈blocks,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M≤U →
      (∀b∈blocks,GlobalCubeAdmissible b) → (∀a,‖Ψ a‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀b∈blocks,∀z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side (b.withCommon ∅)) →
      (∀b∈blocks,∀z∈T b,z≠0) →
      (∑b∈blocks,w b*globalCubeCoefficient p K ell B F side b*
        globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side (2*(J+2)) (T b))≤
      globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ m windows C Cd Ct Γ ε K ell B F M H U A J N side := by sorry
