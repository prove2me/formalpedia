-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_nonzero_source_squarefree_transfer
-- name    : OAI.InitialMeanSquare.initial_nonzero_source_squarefree_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:36:08.404527+00:00
-- url     : https://prove2.me/theorems/57fe2cae-132d-41e0-baa7-8075e2b3ed9f
-- title:
--   Initial Mean Square: initial nonzero source squarefree transfer
-- statement:
--   The Initial Mean Square construction uses the initial nonzero source squarefree transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L438-L490
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L438-L490

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
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
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

theorem OAI.InitialMeanSquare.initial_nonzero_source_squarefree_transfer
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
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O)
        (K : Finset ι → Finset ι → Finset O) (Z H Kmax : ℝ),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z A,
          elementNorm (sourceObservation p x).1 ≤ Kmax) →
        ∃ B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ,
          (∀ ray R j q, 0 ≤ B ray R j q) ∧
          (∀ ray R j q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B ray R j q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            W H (fun C E => (K C E).erase 0)‖ ≤
            C*(∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp A),
              ∑ j ∈ secondLogBinBox (Z*Real.exp A) Kmax,
                initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H A ε j windows (B ray R j)) := by sorry
