-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_high_radial_source
-- name    : OAI.InitialMeanSquare.initial_high_radial_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T23:38:17.755396+00:00
-- url     : https://prove2.me/theorems/ed6ad44b-8c0a-4c24-8e1a-6328baa8a4a8
-- title:
--   Initial Mean Square: initial high radial source
-- statement:
--   The Initial Mean Square construction uses the initial high radial source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L381-L460
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L381-L460

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
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
open OAI.InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem OAI.InitialMeanSquare.initial_high_radial_source
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b θ τ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hθ : 0 < θ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (Z H : ℝ),
      1 ≤ Z → 1 ≤ H → (∀ x,‖Ψ x‖ ≤ 1) →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray R j,s ray R j ⊆ secondLogSector p ∅ F
        (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) j) →
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      C*Z^(-τ) := by sorry
