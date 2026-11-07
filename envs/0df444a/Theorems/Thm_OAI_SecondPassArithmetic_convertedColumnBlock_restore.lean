-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_convertedColumnBlock_restore
-- name    : OAI.SecondPassArithmetic.convertedColumnBlock_restore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:16:54.592211+00:00
-- url     : https://prove2.me/theorems/c663428a-b634-4a2e-b02f-47216a020e19
-- title:
--   Second Pass Arithmetic: converted Column Block restore
-- statement:
--   The Second Pass Arithmetic construction uses the converted Column Block restore property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean#L399-L423
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean#L399-L423

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FirstPassage
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_false
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_true

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG convertedColumnBlock quadraticCrossPhase
  columnPrimeCoprime columnCoefficient_cancel_false columnCoefficient_cancel_true)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

theorem OAI.SecondPassArithmetic.convertedColumnBlock_restore {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    convertedColumnBlock p hp hg S false =
      star (columnCoefficient p hp hcop hg S) * columnG p hp hcop hg S ∧
    convertedColumnBlock p hp hg S true =
      columnCoefficient p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        star (columnG p hp hcop hg S) := by sorry
