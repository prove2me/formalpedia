-- Prove2me | Theorems.Thm_OAI_InitialMeanSquare_initial_harmonic_aggregation
-- name    : OAI.InitialMeanSquare.initial_harmonic_aggregation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:22:49.490363+00:00
-- url     : https://prove2.me/theorems/de6e4e9b-d9f1-4fc9-98a9-ae47dc59dbcd
-- title:
--   Initial Mean Square: initial harmonic aggregation
-- statement:
--   The Initial Mean Square construction uses the initial harmonic aggregation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/HarmonicAggregation.lean#L112-L148
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/HarmonicAggregation.lean#L112-L148

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
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem OAI.InitialMeanSquare.initial_harmonic_aggregation (F : Finset ι) (U K D : ℝ) (hD : 0 ≤ D)
    (a : SecondRayIndex → Finset ι → SecondLogIndex → ℝ)
    (ha : ∀ ray, ∀ R ∈ boundedPrimeSupports p F U, ∀ j ∈ secondLogBinBox U K,
      a ray R j ≤ D/primeProductNorm p R*‖secondRayCoefficient ray‖) :
    (∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F U,
      ∑ j ∈ secondLogBinBox U K,a ray R j) ≤
    D*initialRayMass*((secondLogBinBox U K).card : ℝ)*
      (128*Real.exp 1*(normLogBin U+1 : ℝ)) := by sorry
