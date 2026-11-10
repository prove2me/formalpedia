-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTruncatedSource_eq_bins
-- name    : OAI.SecondPassArithmetic.globalFirstTruncatedSource_eq_bins
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T07:22:22.377954+00:00
-- url     : https://prove2.me/theorems/6b99d8fc-e39e-430c-947d-a4a647a4d5b8
-- title:
--   Second Pass Arithmetic: global First Truncated Source eq bins
-- statement:
--   The Second Pass Arithmetic construction uses the global First Truncated Source eq bins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/PooledRows.lean#L225-L273
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/PooledRows.lean#L225-L273

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem OAI.SecondPassArithmetic.globalFirstTruncatedSource_eq_bins
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (K ell B F M H : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool)
    (hb₁ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    globalFirstTruncatedSource p hp hg hinj pool s
      (fun b => w b*globalFirstCoefficient p K ell B F side b) cutoff Ψ m g W ell side
      (globalFirstPooledRow p K ell B F side) =
      ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinFirstCoefficient K ell B F j : ℂ)*
          globalSecondLiteralBinSource p hp hcop hg (fun x => w x.first) source side j pool Ψ m
            g g W ell (globalPooledRowScale K ell B F j) := by sorry
