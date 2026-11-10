-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_full_uniform_canonicalSource_kernel_tail
-- name    : OAI.SecondPassArithmetic.full_uniform_canonicalSource_kernel_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T23:46:24.702243+00:00
-- url     : https://prove2.me/theorems/f6efc89a-9860-4fd7-887f-dfe3dd3ef096
-- title:
--   Second Pass Arithmetic: full uniform canonical Source kernel tail
-- statement:
--   The Second Pass Arithmetic construction uses the full uniform canonical Source kernel tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DualZeroMode.lean#L624-L684
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/DualZeroMode.lean#L624-L684

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

theorem OAI.SecondPassArithmetic.full_uniform_canonicalSource_kernel_tail (A : ℕ) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι),b.Admissible → ∀ C D:Finset ι,Disjoint C b.support →
      ∀(Ψ₁ Ψ₂:O→*ℂ),(∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      ∀(m₁ m₂ f:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (G₁ G₂ M₁ M₂ Ksrc K ell:ℝ),
      0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
      let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
      let U₁:=X₁*Real.exp M₁
      let U₂:=X₂*Real.exp M₂
      let slow:=Ksrc/(primeProductNorm p D*primeProductNorm p
        (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*U₁*U₂)
      let T:=firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun S=>g₁ (columnLog p ell S)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun S=>g₂ (columnLog p ell S)))
        W (fun _=>1) (fun _=>1) 1 1 Ksrc
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Ksrc)*
        ((Ctail*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+(Ksrc/K)/Real.exp (M₁+M₂))^A)) := by sorry
