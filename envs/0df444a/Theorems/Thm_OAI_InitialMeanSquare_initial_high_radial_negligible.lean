-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_high_radial_negligible
-- name    : OAI.InitialMeanSquare.initial_high_radial_negligible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T23:40:35.29272+00:00
-- url     : https://prove2.me/theorems/9b949958-2ab4-4f20-a981-44e4778ad605
-- title:
--   Initial Mean Square: initial high radial negligible
-- statement:
--   The Initial Mean Square construction uses the initial high radial negligible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L179-L235
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L179-L235

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
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

theorem OAI.InitialMeanSquare.initial_high_radial_negligible (θ τ A Vmax Cs Ccap : ℝ) (N : ℕ)
    (hN : 38+τ ≤ θ*(N : ℝ)) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hCs : 0 ≤ Cs) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
      (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε : ℝ),
      1 ≤ Z → 1 ≤ H → 0 < U → 0 < Kmax → ε ≤ 1 →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
        s ray R j ⊆ secondLogSector p ∅ F K R Z M j) →
      ∀ (V₁ V₂ : ℝ → ℂ),
      (∀ t,‖V₁ t‖ ≤ Vmax) → (∀ t,‖V₂ t‖ ≤ Vmax) →
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) → (∀ t,V₂ t ≠ 0 → |t| ≤ A) →
      ∀ (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J : ℕ),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q) →
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
        Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) →
      initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤ C*Z^(-τ) := by sorry
