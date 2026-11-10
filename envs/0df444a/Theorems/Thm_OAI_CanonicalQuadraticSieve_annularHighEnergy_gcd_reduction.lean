-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_annularHighEnergy_gcd_reduction
-- name    : OAI.CanonicalQuadraticSieve.annularHighEnergy_gcd_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T06:02:11.820192+00:00
-- url     : https://prove2.me/theorems/bed0a7db-e64f-4581-b0f2-3139b51a3ded
-- title:
--   Canonical Quadratic Sieve: annular High Energy gcd reduction
-- statement:
--   The Canonical Quadratic Sieve construction uses the annular High Energy gcd reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean#L470-L481
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean#L470-L481

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
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
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy

theorem OAI.CanonicalQuadraticSieve.annularHighEnergy_gcd_reduction (M N K H : ℝ) (hN : 1≤N) (hH : 0<H)
    (ε : ℝ) (hε : 0<ε) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ 16*((∑c : EisensteinEPrimaryPhase.Coord,
      ∑D∈(gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H),
        ‖annularRayGcdBlock M N K D c a‖) +
      highKernelNorm (2*M) (N/H) K*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by sorry
