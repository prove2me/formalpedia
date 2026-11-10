-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_sum_globalFirstExpansionPool
-- name    : OAI.SecondPassArithmetic.sum_globalFirstExpansionPool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T07:18:56.619092+00:00
-- url     : https://prove2.me/theorems/96f332f6-4816-4766-b87d-7d20a450f1fb
-- title:
--   Second Pass Arithmetic: sum global First Expansion Pool
-- statement:
--   The Second Pass Arithmetic construction uses the sum global First Expansion Pool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean#L438-L455
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/LiteralSources.lean#L438-L455

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
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
variable {ι : Type*} [DecidableEq ι]

theorem OAI.SecondPassArithmetic.sum_globalFirstExpansionPool {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (f : GlobalSecondData ι → M) :
    ∑ x∈globalFirstExpansionPool pool s cutoff,f x =
    ∑ b∈s,∑ x∈secondExpansionPool (globalFirstRawPool pool b) (cutoff b),f (b.append x) := by sorry
