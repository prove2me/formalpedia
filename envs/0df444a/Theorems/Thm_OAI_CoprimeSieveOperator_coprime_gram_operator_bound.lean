-- Prove2me | Theorems.Thm_OAI_CoprimeSieveOperator_coprime_gram_operator_bound
-- name    : OAI.CoprimeSieveOperator.coprime_gram_operator_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:16:02.283963+00:00
-- url     : https://prove2.me/theorems/286db998-53f0-4bf7-9333-5a469a0585fc
-- title:
--   Coprime Sieve Operator: coprime gram operator bound
-- statement:
--   The Coprime Sieve Operator construction uses the coprime gram operator bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CrossFactorization.lean#L480-L518
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CrossFactorization.lean#L480-L518

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
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
open OAI.CoprimeSieveOperator
open FiniteSieveOperator CoprimeMobiusExtension

theorem OAI.CoprimeSieveOperator.coprime_gram_operator_bound {ι m n : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by sorry
