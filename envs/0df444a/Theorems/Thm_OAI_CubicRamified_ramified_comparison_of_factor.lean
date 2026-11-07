-- Prove2me | Theorems.Thm_OAI_CubicRamified_ramified_comparison_of_factor
-- name    : OAI.CubicRamified.ramified_comparison_of_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:23.204441+00:00
-- url     : https://prove2.me/theorems/5ee56fb2-6824-4414-add1-4330254c83cf
-- title:
--   Cubic Ramified: ramified comparison of factor
-- statement:
--   The Cubic Ramified construction uses the ramified comparison of factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Reciprocity/CubicJacobi.lean#L437-L457
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Reciprocity/CubicJacobi.lean#L437-L457

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
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
open scoped BigOperators Classical
open OAI.CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

theorem OAI.CubicRamified.ramified_comparison_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : u ≠ 0) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by sorry
