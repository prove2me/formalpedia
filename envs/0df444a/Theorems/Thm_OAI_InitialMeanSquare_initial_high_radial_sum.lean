-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_high_radial_sum
-- name    : OAI.InitialMeanSquare.initial_high_radial_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T23:37:55.613107+00:00
-- url     : https://prove2.me/theorems/ed0c4183-9168-4a78-9a53-0875ee9e9a87
-- title:
--   Initial Mean Square: initial high radial sum
-- statement:
--   The Initial Mean Square construction uses the initial high radial sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L109-L149
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L109-L149

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
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (OAI.InitialMeanSquare.O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hc hinj

theorem OAI.InitialMeanSquare.initial_high_radial_sum (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε θ A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (hs : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
      s ray R j ⊆ secondLogSector p ∅ F K R Z M j)
    (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J N : ℕ)
    (hB : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q)
    (hdec : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤
      (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := by sorry
