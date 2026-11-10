-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_canonicalCubeFirstBlock_input_transfer
-- name    : OAI.SecondPassArithmetic.canonicalCubeFirstBlock_input_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:56:34.138631+00:00
-- url     : https://prove2.me/theorems/b0c32e77-2c72-4fb9-ba92-adce10c48d6e
-- title:
--   Second Pass Arithmetic: canonical Cube First Block input transfer
-- statement:
--   The Second Pass Arithmetic construction uses the canonical Cube First Block input transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/QuantitativePassage.lean#L181-L300
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/QuantitativePassage.lean#L181-L300

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
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
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.SecondPassArithmetic.canonicalCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by sorry
