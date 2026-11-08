-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_postCommonSmoothPair_fixed_tests
-- name    : OAI.SecondPassArithmetic.postCommonSmoothPair_fixed_tests
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:20:27.750993+00:00
-- url     : https://prove2.me/theorems/f39b2748-0bb1-4e6f-9db8-5ef0741683b8
-- title:
--   Second Pass Arithmetic: post Common Smooth Pair fixed tests
-- statement:
--   The Second Pass Arithmetic construction uses the post Common Smooth Pair fixed tests property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/FrequencyTwists.lean#L371-L479
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/FrequencyTwists.lean#L371-L479

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SecondPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_FrequencyTwists
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
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog firstLogDensity)
open JointLogSeparation (outerWindow fixedColumnTest)
open FourierBridge (logPhase)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem OAI.SecondPassArithmetic.postCommonSmoothPair_fixed_tests
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ a a' : ℝ,
      outerWindow V z ud ue uv kap * V 5 a * V 6 a' * A₁ (z+a) * A₂ (z+a') *
        EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp (kap-ud-2*ue-2*uv-a-a')) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
          logPhase t₃ (kap-ud-2*ue-2*uv) *
          fixedColumnTest (V 5) (t₁-t₃) a * fixedColumnTest (V 6) (t₂-t₃) a' *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) :
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
        logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂ := by sorry
