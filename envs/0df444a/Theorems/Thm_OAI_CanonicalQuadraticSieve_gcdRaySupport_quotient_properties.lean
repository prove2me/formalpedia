-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_gcdRaySupport_quotient_properties
-- name    : OAI.CanonicalQuadraticSieve.gcdRaySupport_quotient_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-08T19:52:38.988617+00:00
-- url     : https://prove2.me/theorems/ef920342-8ba3-46ec-8b7b-b51a902f2625
-- title:
--   Canonical Quadratic Sieve: gcd Ray Support quotient properties
-- statement:
--   The Canonical Quadratic Sieve construction uses the gcd Ray Support quotient properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean#L607-L635
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean#L607-L635

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem OAI.CanonicalQuadraticSieve.gcdRaySupport_quotient_properties (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (hD : D≠0)
    (c : EisensteinEPrimaryPhase.Coord) :
    let cols := fun j : gcdRaySupport (fun I : idealRange N => I.val) a D c =>
      idealQuotient D j.val.val
    Function.Injective cols ∧
    (∀ j, Admissible (cols j) ∧
      (X/(Ideal.absNorm D:ℝ))/2≤(Ideal.absNorm (cols j):ℝ) ∧
      (Ideal.absNorm (cols j):ℝ)≤X/(Ideal.absNorm D:ℝ) ∧
      IsCoprime (commonMaskIdeal D) (cols j)) ∧
    (∀ j k, columnRay (cols j)=columnRay (cols k)) := by sorry
