-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_divisor_block_phase_bound
-- name    : OAI.CanonicalQuadraticSieve.canonical_divisor_block_phase_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:43:59.415199+00:00
-- url     : https://prove2.me/theorems/db2ed609-5be5-4b86-a2ad-2be3f38b4b38
-- title:
--   Canonical Quadratic Sieve: canonical divisor block phase bound
-- statement:
--   The Canonical Quadratic Sieve construction uses the canonical divisor block phase bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DivisorBlocks.lean#L529-L557
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DivisorBlocks.lean#L529-L557

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
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
open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open OAI.CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem OAI.CanonicalQuadraticSieve.canonical_divisor_block_phase_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    (∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by sorry
