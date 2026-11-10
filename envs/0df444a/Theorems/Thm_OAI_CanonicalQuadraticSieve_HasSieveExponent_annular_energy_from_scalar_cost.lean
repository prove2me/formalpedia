-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_annular_energy_from_scalar_cost
-- name    : OAI.CanonicalQuadraticSieve.HasSieveExponent.annular_energy_from_scalar_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T06:05:08.388471+00:00
-- url     : https://prove2.me/theorems/9b331a02-4430-4f61-8261-ab018928dc01
-- title:
--   Has Sieve Exponent: annular energy from scalar cost
-- statement:
--   The Has Sieve Exponent construction uses the annular energy from scalar cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean#L483-L537
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean#L483-L537

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

theorem OAI.CanonicalQuadraticSieve.HasSieveExponent.annular_energy_from_scalar_cost {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP CH : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧ 0<CH ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N K T H C : ℝ),
      1≤M → 1≤N → 1≤K → 4≤T → 0<H → H≤N/2 → 0≤C →
      (∀D∈gcdPool (fun J : idealRange N => J.val), (Ideal.absNorm D:ℝ)≤H →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
          (commonMaskIdeal D) K (N/(Ideal.absNorm D:ℝ)) M T
          (fun _ : Unit => (1:ℂ)) QuadraticInitialBound.annularSieveCutoff≤C) →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N K a ≤
        16*((C/6)*(divisorConstant ε hε*N^ε) +
          (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
            (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑J,‖a J‖^2 := by sorry
