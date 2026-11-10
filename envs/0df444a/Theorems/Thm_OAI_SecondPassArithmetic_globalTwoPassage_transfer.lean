-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalTwoPassage_transfer
-- name    : OAI.SecondPassArithmetic.globalTwoPassage_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T08:59:28.224531+00:00
-- url     : https://prove2.me/theorems/f4be5637-c06e-481a-8664-920c4b26f170
-- title:
--   Second Pass Arithmetic: global Two Passage transfer
-- statement:
--   The Second Pass Arithmetic construction uses the global Two Passage transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/PowerfulParts.lean#L571-L630
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/PowerfulParts.lean#L571-L630

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SquarefreeTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_PowerfulParts
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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.SecondPassArithmetic.globalTwoPassage_transfer
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Ct₁ C₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H Ymax : ℝ),
      0≤Γ → 0<K → 0<ell → 0<B → 0<F → 0≤H → 0≤Ymax →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*Ymax^deltaLoss*
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₁ m₁ g₁ V₁ windows₁ C₁ Ct₁ Γ ε K ell B F M₁ H A J N true) *
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₂ m₂ g₂ V₂ windows₂ C₂ Ct₂ Γ ε K ell B F M₂ H A J N false) := by sorry
