-- Prove2me | Theorems.Thm_OAI_CoprimeBilinearSieve_coprime_bilinear_operator_bound
-- name    : OAI.CoprimeBilinearSieve.coprime_bilinear_operator_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:32:22.496405+00:00
-- url     : https://prove2.me/theorems/e3b4572b-2cab-4186-8e69-213300dc1fdf
-- title:
--   Coprime Bilinear Sieve: coprime bilinear operator bound
-- statement:
--   The Coprime Bilinear Sieve construction uses the coprime bilinear operator bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean#L119-L174
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean#L119-L174

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
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
open OAI.CoprimeBilinearSieve
open FiniteSieveOperator CoprimeSieveOperator CoprimeMobiusExtension

theorem OAI.CoprimeBilinearSieve.coprime_bilinear_operator_bound {ι m n p : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (B : Finset ι) (left : n → Finset ι) (right : p → Finset ι)
    (hl : ∀ j, left j ⊆ B) (hr : ∀ k, right k ⊆ B)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2) := by sorry
