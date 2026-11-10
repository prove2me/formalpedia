-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_bin_transfer
-- name    : OAI.InitialMeanSquare.initial_bin_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:25:48.953217+00:00
-- url     : https://prove2.me/theorems/c0e4ebd8-a19d-42df-a611-5de8e155ad00
-- title:
--   Initial Mean Square: initial bin transfer
-- statement:
--   The Initial Mean Square construction uses the initial bin transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L179-L235
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L179-L235

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_OutsideIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
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
open OAI.InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.InitialMeanSquare.initial_bin_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (Z H M : ℝ) (j : SecondLogIndex),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        let s := secondLogSector p ∅ F K R Z M j
        let X := initialLogColumn Z (primeProductNorm p R) j
        let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
        ∃ B : Frequency → ℝ,
          (∀ q, 0 ≤ B q) ∧
          (∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) W H‖ ≤
          (C*H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by sorry
