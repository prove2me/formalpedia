-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_sector_fixed_profiles
-- name    : OAI.InitialMeanSquare.initial_sector_fixed_profiles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:53:10.630079+00:00
-- url     : https://prove2.me/theorems/20571416-eb53-4535-927a-28d280e3fd86
-- title:
--   Initial Mean Square: initial sector fixed profiles
-- statement:
--   The Initial Mean Square construction uses the initial sector fixed profiles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/SmoothTests.lean#L357-L403
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/SmoothTests.lean#L357-L403

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
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
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open SecondPassIntegration (elementNorm)

theorem OAI.InitialMeanSquare.initial_sector_fixed_profiles
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU₁ : ∀t,g₁ t≠0→U t=1) (hU₂ : ∀t,g₂ t≠0→U t=1)
    (hg₁ : ∀t,g₁ t≠0→|t|≤A) (hg₂ : ∀t,g₂ t≠0→|t|≤A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<E → 0<V → 0<X → 0<K →
        (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
          (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
          (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H =
        initialSourceSum p hp hcop hg s (sourceWeight p hp hcop hg Ψ m ray Z H)
          F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r) A₁ A₂ W windows
          (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K)
          X X (H*K/(E^2*V^2*X^2)) := by sorry
