-- Prove2me | Theorems.Thm_OAI_CubicEisenstein_integralConjugatePullback_ae
-- name    : OAI.CubicEisenstein.integralConjugatePullback_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:16:31.908204+00:00
-- url     : https://prove2.me/theorems/4a880427-414d-4673-be8b-e0ee53bc88fd
-- title:
--   Cubic Eisenstein: integral Conjugate Pullback ae
-- statement:
--   The Cubic Eisenstein construction uses the integral Conjugate Pullback ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CoverTrace.lean#L488-L494
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/CoverTrace.lean#L488-L494

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_IntegralCover
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoverTrace
set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O

theorem OAI.CubicEisenstein.integralConjugatePullback_ae {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : Lp ℂ 2 (integralQuotientVolume J)) :
    integralConjugatePullback e g he hH hJ F=ᵐ[integralQuotientVolume H]
      fun q=>F (integralConjugateMap e g he q) := by sorry
