-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_HasInitialCanonicalDensity_retained_density
-- name    : OAI.InitialMeanSquare.HasInitialCanonicalDensity.retained_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:07:10.133321+00:00
-- url     : https://prove2.me/theorems/2a1309d4-b11c-45a0-868d-092dc134f5cf
-- title:
--   Has Initial Canonical Density: retained density
-- statement:
--   The Has Initial Canonical Density construction uses the retained density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/RetainedDensity.lean#L287-L390
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/RetainedDensity.lean#L287-L390

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
set_option autoImplicit false
open OAI
noncomputable section
open OAI.InitialMeanSquare
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
open MeasureTheory
open scoped BigOperators Classical ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

theorem OAI.InitialMeanSquare.HasInitialCanonicalDensity.retained_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (a b σ θ ν η : ℝ) (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ J : ℕ,∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
      ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧ ∀ (D : ℕ) (Z : ℝ)
        (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (j : SecondLogIndex)
        (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
        1 ≤ Z → Cpool*Z^E ≤ D →
        R ∈ boundedPrimeSupports (outsidePrime S D) Finset.univ (Z*Real.exp (initialErrorWindow a b)) →
        j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z (Z^(1+σ))) →
        initialRadial Z (Z^(1+σ)) (primeProductNorm (outsidePrime S D) R) j ≤ Z^θ →
        (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
          z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2) →
        outsideCanonicalDensity χ S hbad D ray R T V₁ V₂
          (initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j) J ≤
        C*Z^η*(initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j*initialLogLabel j)^2 := by sorry
