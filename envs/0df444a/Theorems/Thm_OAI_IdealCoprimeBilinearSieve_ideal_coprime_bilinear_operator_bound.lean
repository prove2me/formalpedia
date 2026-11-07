-- Prove2me | Theorems.Thm_OAI_IdealCoprimeBilinearSieve_ideal_coprime_bilinear_operator_bound
-- name    : OAI.IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:33:20.575214+00:00
-- url     : https://prove2.me/theorems/49a8f3e1-cae6-4836-9632-d2da099e8b56
-- title:
--   Ideal Coprime Bilinear Sieve: ideal coprime bilinear operator bound
-- statement:
--   The Ideal Coprime Bilinear Sieve construction uses the ideal coprime bilinear operator bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean#L195-L229
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean#L195-L229

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
open OAI.IdealCoprimeBilinearSieve
open IdealMobiusDivisorSum IdealCoprimeSieveOperator FiniteSieveOperator

theorem OAI.IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε)
    (left : n → Ideal O) (right : p → Ideal O)
    (hl0 : ∀ j, left j ≠ 0) (hr0 : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (_hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * (supportConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * (supportConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by sorry
