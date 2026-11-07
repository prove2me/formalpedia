-- Prove2me | Theorems.Thm_OAI_IdealCoprimeSieveOperator_actual_quadratic_coprime_gram_bound
-- name    : OAI.IdealCoprimeSieveOperator.actual_quadratic_coprime_gram_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:47:57.846074+00:00
-- url     : https://prove2.me/theorems/68fda41a-f399-467e-85bc-137fd98f6f0e
-- title:
--   Ideal Coprime Sieve Operator: actual quadratic coprime gram bound
-- statement:
--   The Ideal Coprime Sieve Operator construction uses the actual quadratic coprime gram bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CrossFactorization.lean#L586-L601
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CrossFactorization.lean#L586-L601

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
open OAI.IdealCoprimeSieveOperator
open IdealMobiusDivisorSum CoprimeSieveOperator FiniteSieveOperator
open UniqueFactorizationMonoid
open ConcretePrimeRowBridge

theorem OAI.IdealCoprimeSieveOperator.actual_quadratic_coprime_gram_bound {m : Type*}
    [Fintype m] [DecidableEq m]
    (ε : ℝ) (hε : 0 < ε)
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ normalizedFactors I, goodLambda ∉ P)
    (r : m → O) (N : ℝ) (hN : 0 ≤ N)
    (hnorm : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ N)
    (a : F → ℂ) (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    let A : Matrix m F ℂ := fun i J => (idealSexticRow F hFpos hFgood J.val (r i)) ^ 3
    ‖∑ i, w i * (∑ J : F, ∑ columnTwo : F,
      if IsCoprime J.val columnTwo.val then star (A i J * a J) * (A i columnTwo * a columnTwo) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) * ∑ J : F, ‖a J‖ ^ 2 := by sorry
