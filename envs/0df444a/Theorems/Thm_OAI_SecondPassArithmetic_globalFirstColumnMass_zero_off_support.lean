-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalFirstColumnMass_zero_off_support
-- name    : OAI.SecondPassArithmetic.globalFirstColumnMass_zero_off_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:59:42.973707+00:00
-- url     : https://prove2.me/theorems/9d453c00-587a-4269-8af6-db35abc34214
-- title:
--   Second Pass Arithmetic: global First Column Mass zero off support
-- statement:
--   The Second Pass Arithmetic construction uses the global First Column Mass zero off support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean#L247-L254
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/NormalizedMass.lean#L247-L254

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DivisorTargets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_NormalizedMass
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
open FirstPassCubeLabels (primeProductNorm)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})
include hp

theorem OAI.SecondPassArithmetic.globalFirstColumnMass_zero_off_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g : 𝓢(ℝ,ℂ)) (ell M U : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U) (side : Bool)
    (hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)) :
    globalFirstColumnMass p hg pool b Ψ m g ell side=0 := by sorry
