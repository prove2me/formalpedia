-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_original_entry_factor
-- name    : OAI.CanonicalQuadraticSieve.original_entry_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:42:21.259196+00:00
-- url     : https://prove2.me/theorems/bd7023b8-9c75-4094-b32f-357099e570ab
-- title:
--   Canonical Quadratic Sieve: original entry factor
-- statement:
--   The Canonical Quadratic Sieve construction uses the original entry factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DivisorBlocks.lean#L202-L211
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DivisorBlocks.lean#L202-L211

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
open OAI.CanonicalQuadraticSieve
open IdealDivisorBilinearBlocks CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

theorem OAI.CanonicalQuadraticSieve.original_entry_factor {m n : Type*} (rows : m → Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (D : Ideal O) (i : m) (j : n) :
    quadraticRow (cols j) (primaryGenerator (rows i)) * (if D ∣ cols j then a j else 0) =
      quadraticRow D (primaryGenerator (rows i)) *
        (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) := by sorry
