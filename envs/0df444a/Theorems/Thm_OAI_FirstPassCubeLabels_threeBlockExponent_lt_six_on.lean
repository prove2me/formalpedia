-- Prove2me | Theorems.Thm_OAI_FirstPassCubeLabels_threeBlockExponent_lt_six_on
-- name    : OAI.FirstPassCubeLabels.threeBlockExponent_lt_six_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T23:37:02.315056+00:00
-- url     : https://prove2.me/theorems/7a1728b6-83b3-4828-91b7-30b88a65c127
-- title:
--   First Pass Cube Labels: three Block Exponent lt six on
-- statement:
--   The First Pass Cube Labels construction uses the three Block Exponent lt six on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L490-L494
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean#L490-L494

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
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
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.FirstPassCubeLabels.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem OAI.FirstPassCubeLabels.threeBlockExponent_lt_six_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by sorry
