-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_globalCubeFirstTargets_norm_bound
-- name    : OAI.SecondPassArithmetic.globalCubeFirstTargets_norm_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T09:51:38.362081+00:00
-- url     : https://prove2.me/theorems/af01aff9-d67e-4eb0-9132-f951a8b8922b
-- title:
--   Second Pass Arithmetic: global Cube First Targets norm bound
-- statement:
--   The Second Pass Arithmetic construction uses the global Cube First Targets norm bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L643-L653
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/LogarithmicBins.lean#L643-L653

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_LogarithmicBins
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
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
include hp

theorem OAI.SecondPassArithmetic.globalCubeFirstTargets_norm_bound (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : ∀ x∈s,(Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ∀ x∈s,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) :
    (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by sorry
