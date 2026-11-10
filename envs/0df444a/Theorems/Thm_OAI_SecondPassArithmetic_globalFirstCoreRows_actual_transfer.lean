-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalFirstCoreRows_actual_transfer
-- name    : OAI.SecondPassArithmetic.globalFirstCoreRows_actual_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T07:24:59.206897+00:00
-- url     : https://prove2.me/theorems/ca44a063-7149-476f-9d63-ea1e219ac048
-- title:
--   Second Pass Arithmetic: global First Core Rows actual transfer
-- statement:
--   The Second Pass Arithmetic construction uses the global First Core Rows actual transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/PooledRows.lean#L363-L437
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/PooledRows.lean#L363-L437

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem OAI.SecondPassArithmetic.globalFirstCoreRows_actual_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0≤C ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let cutoff := globalFirstConcreteCutoff p K ell B F M H side
      let source := globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      let profile := firstCoreModeProfile g V side t
      (∑ b∈s,weight b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
        globalFirstCoreCorrection p g V ell side t b)) ≤
      globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side +
      ‖globalFirstSourceZero p hg pool s (fun b => weight b) cutoff Ψmode m profile rowMajorant ell side
        (globalFirstPooledRow p K ell B F side)‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => weight b) cutoff Ψmode m profile rowMajorant ell side
        (globalFirstPooledRow p K ell B F side)‖ := by sorry
