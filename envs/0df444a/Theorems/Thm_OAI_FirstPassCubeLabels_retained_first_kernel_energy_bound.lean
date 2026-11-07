-- Prove2me | Theorems.Thm_OAI_FirstPassCubeLabels_retained_first_kernel_energy_bound
-- name    : OAI.FirstPassCubeLabels.retained_first_kernel_energy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:08:41.898715+00:00
-- url     : https://prove2.me/theorems/1e9af82d-c524-4bdd-bb30-3a01680d336b
-- title:
--   First Pass Cube Labels: retained first kernel energy bound
-- statement:
--   The First Pass Cube Labels construction uses the retained first kernel energy bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/KernelEnergy.lean#L464-L545
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/KernelEnergy.lean#L464-L545

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
set_option autoImplicit false
open OAI
noncomputable section
open OAI.FirstPassCubeLabels
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
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.FirstPassCubeLabels.retained_first_kernel_energy_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale →
      ∀ (Ω : Finset (Finset ι × O)) (w : Finset ι × O → ℂ),
      (∀ x ∈ Ω, x.2 ≠ 0) → ∃ b : (Finset ι × O) → 𝓢(ℝ, ℂ),
      (∀ x ∈ Ω, Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b x t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2) ^ A *
            (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b x t‖) ≤ K) ∧
      ‖∑ x ∈ Ω, (w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) := by sorry
