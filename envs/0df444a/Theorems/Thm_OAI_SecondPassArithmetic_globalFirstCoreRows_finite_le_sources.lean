-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalFirstCoreRows_finite_le_sources
-- name    : OAI.SecondPassArithmetic.globalFirstCoreRows_finite_le_sources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T07:19:47.820203+00:00
-- url     : https://prove2.me/theorems/9b9566d0-82dc-40c7-a9fe-bae99d643c0c
-- title:
--   Second Pass Arithmetic: global First Core Rows finite le sources
-- statement:
--   The Second Pass Arithmetic construction uses the global First Core Rows finite le sources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean#L608-L649
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean#L608-L649

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CompactProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem OAI.SecondPassArithmetic.globalFirstCoreRows_finite_le_sources
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (hw : ∀ b∈s,0 ≤ w b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b)
    (T : GlobalFirstData ι → Finset O)
    (hT : ∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y b)
    (hT0 : ∀ b∈s,∀ z∈T b,z ≠ 0) :
    (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      ‖globalFirstTruncatedSource p hp hg hinj pool s (fun b => w b)
        (fun b G E => (cutoff b G E).erase 0) (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceZero p hg pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ := by sorry
