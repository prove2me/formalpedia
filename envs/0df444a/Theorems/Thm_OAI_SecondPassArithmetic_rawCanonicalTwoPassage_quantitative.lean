-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_rawCanonicalTwoPassage_quantitative
-- name    : OAI.SecondPassArithmetic.rawCanonicalTwoPassage_quantitative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:25:34.042505+00:00
-- url     : https://prove2.me/theorems/67605294-2bcc-437a-be65-733b2114bf70
-- title:
--   Second Pass Arithmetic: raw Canonical Two Passage quantitative
-- statement:
--   The Second Pass Arithmetic construction uses the raw Canonical Two Passage quantitative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/HarmonicAggregation.lean#L413-L490
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/HarmonicAggregation.lean#L413-L490

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialWindows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HarmonicAggregation
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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.SecondPassArithmetic.rawCanonicalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (hWin₁ : ∀ t,g₁ t≠0 → V₁ t=1) (hWin₂ : ∀ t,g₂ t≠0 → V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
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
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by sorry
