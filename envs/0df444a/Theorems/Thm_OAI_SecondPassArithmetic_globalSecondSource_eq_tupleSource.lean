-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalSecondSource_eq_tupleSource
-- name    : OAI.SecondPassArithmetic.globalSecondSource_eq_tupleSource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-08T19:35:59.951221+00:00
-- url     : https://prove2.me/theorems/b9032e55-3294-4b20-a4bb-2f2e5d7c81aa
-- title:
--   Second Pass Arithmetic: global Second Source eq tuple Source
-- statement:
--   The Second Pass Arithmetic construction uses the global Second Source eq tuple Source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/QuotientTopology.lean#L273-L291
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/QuotientTopology.lean#L273-L291

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_HighKernelGeometry
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
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
open OAI.SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)
attribute [local instance] OAI.SecondPassArithmetic._p2m_local_instance_9dd05bc69a_244
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem OAI.SecondPassArithmetic.globalSecondSource_eq_tupleSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (s : Finset (GlobalSecondData ι)) (q : Ideal O × Ideal O × Ideal O)
    (hs : ∀ x∈s,GlobalSecondAdmissible x) (hq : ∀ x∈s,globalSecondFixedTriple p x=q)
    (w : GlobalSecondData ι → ℂ) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ R : ℝ) :
    globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    tupleSourceSum p hp hcop hg (s.image (globalSecondTuple p))
      (w ∘ globalSecondRecover p s) (globalSecondLabel p ∘ globalSecondRecover p s)
      F Ψ₁ Ψ₂ m A₁ A₂ W V (z ∘ globalSecondRecover p s) (ud ∘ globalSecondRecover p s)
      (ue ∘ globalSecondRecover p s) (uv ∘ globalSecondRecover p s) (kap ∘ globalSecondRecover p s) X₁ X₂ R := by sorry
