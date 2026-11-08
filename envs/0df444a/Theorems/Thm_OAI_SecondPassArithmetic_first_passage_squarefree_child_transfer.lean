-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_first_passage_squarefree_child_transfer
-- name    : OAI.SecondPassArithmetic.first_passage_squarefree_child_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:39:43.348495+00:00
-- url     : https://prove2.me/theorems/e1f3aa89-c0f7-49be-8786-541a5f3f079b
-- title:
--   Second Pass Arithmetic: first passage squarefree child transfer
-- statement:
--   The Second Pass Arithmetic construction uses the first passage squarefree child transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/SquarefreeTransfer.lean#L285-L375
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/SquarefreeTransfer.lean#L285-L375

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicSectors
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SquarefreeTransfer
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
open MeasureTheory
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity
  actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

theorem OAI.SecondPassArithmetic.first_passage_squarefree_child_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B C D : Finset ι) (hFB : Disjoint F B) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O)
    (hΨ₁ : ∀ a, ‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a, ‖Ψ₂ a‖ ≤ 1)
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ))
    (U₁ U₂ : ℝ → ℂ) (hUc₁ : HasCompactSupport U₁) (hUs₁ : ContDiff ℝ ∞ U₁)
    (hUc₂ : HasCompactSupport U₂) (hUs₂ : ContDiff ℝ ∞ U₂)
    (hU₁ : ∀ t, g₁ t ≠ 0 → U₁ t=1) (hU₂ : ∀ t, g₂ t ≠ 0 → U₂ t=1)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ N₁ N₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ M₁) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ M₂)
    (hV₁ : ∀ t, V₁ t ≠ 0 → |t| ≤ N₁) (hV₂ : ∀ t, V₂ t ≠ 0 → |t| ≤ N₂)
    (ε deltaLoss : ℝ) (hε : 0 < ε) (hδ : 0 < deltaLoss) (tailOrder decayOrder J : ℕ) :
    ∃ (data₁ data₂ : SquarefreeBudgetData) (K₀ : ℝ), 0 ≤ K₀ ∧
      ∀ (lengthScale : ℝ), 0 < lengthScale → ∀ (s : Finset (Ideal O × O)) (T : Finset O)
        (w : Ideal O × O → ℂ) (M Y Z : ℝ),
      0 ≤ M → 0 < Y → 0 ≤ Z →
      (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B (fun i => v₁ i+v₂ i) ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1)) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by sorry
