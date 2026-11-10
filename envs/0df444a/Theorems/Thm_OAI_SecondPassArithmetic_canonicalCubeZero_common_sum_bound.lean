-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_canonicalCubeZero_common_sum_bound
-- name    : OAI.SecondPassArithmetic.canonicalCubeZero_common_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T23:40:35.396263+00:00
-- url     : https://prove2.me/theorems/303be48b-6c36-45d9-983c-eb2edc9ffc40
-- title:
--   Second Pass Arithmetic: canonical Cube Zero common sum bound
-- statement:
--   The Second Pass Arithmetic construction uses the canonical Cube Zero common sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DualZeroMode.lean#L439-L489
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DualZeroMode.lean#L439-L489

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DualZeroMode
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
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))
  (hc : ∀i,ringChar (OAI.SecondPassArithmetic.O⧸Ideal.span {p i})≠2)
include hinj
include hc

theorem OAI.SecondPassArithmetic.canonicalCubeZero_common_sum_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ ell K M : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hell : 0<ell)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) (hgM : ∀t,g₁ t≠0→t≤M) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (128*(ell*Real.exp M))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by sorry
