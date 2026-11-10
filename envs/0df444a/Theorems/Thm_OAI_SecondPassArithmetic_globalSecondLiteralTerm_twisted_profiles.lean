-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalSecondLiteralTerm_twisted_profiles
-- name    : OAI.SecondPassArithmetic.globalSecondLiteralTerm_twisted_profiles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T06:28:49.627289+00:00
-- url     : https://prove2.me/theorems/cbfb7544-00a9-4d44-9f3a-2702ce16e446
-- title:
--   Second Pass Arithmetic: global Second Literal Term twisted profiles
-- statement:
--   The Second Pass Arithmetic construction uses the global Second Literal Term twisted profiles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean#L598-L687
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CompactProfiles.lean#L598-L687

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_halfNormalization_twist
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply


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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM frequencyTwist frequencyTwist_apply halfNormalization_twist)
open SecondPassFiber (newRow)

theorem OAI.SecondPassArithmetic.globalSecondLiteralTerm_twisted_profiles
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU₁ : ∀ t,g₁ t ≠ 0 → U t=1) (hU₂ : ∀ t,g₂ t ≠ 0 → U t=1)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i,lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀ i,lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (θ₁ θ₂ ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι),
        0 < ell → x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
        let j := globalScaleIndex p side x
        globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x =
          globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x *
          postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x)
            (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (globalSecondRawMask p m x)
            (globalSecondLabel p x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
            (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows (globalBinZ p ell side j x) (globalBinUd p j x)
            (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by sorry
