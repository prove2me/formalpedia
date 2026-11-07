-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_primaryGenerator_inj_on_admissible
-- name    : OAI.CanonicalQuadraticSieve.primaryGenerator_inj_on_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:35:32.415328+00:00
-- url     : https://prove2.me/theorems/c13accf3-352f-456e-87c4-686a14cf964f
-- title:
--   Canonical Quadratic Sieve: primary Generator inj on admissible
-- statement:
--   The Canonical Quadratic Sieve construction uses the primary Generator inj on admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean#L84-L89
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean#L84-L89

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
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
open OAI.CanonicalQuadraticSieve
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT

theorem OAI.CanonicalQuadraticSieve.primaryGenerator_inj_on_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J) (heq : primaryGenerator I = primaryGenerator J) : I = J := by sorry
