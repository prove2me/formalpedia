-- Prove2me | Theorems.Thm_OAI_IdealCoprimeBilinearSieve_support_weighted_energy_bound
-- name    : OAI.IdealCoprimeBilinearSieve.support_weighted_energy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:33:17.672198+00:00
-- url     : https://prove2.me/theorems/3620179a-c5b5-45f3-8eff-ec1c4eefab9e
-- title:
--   Ideal Coprime Bilinear Sieve: support weighted energy bound
-- statement:
--   The Ideal Coprime Bilinear Sieve construction uses the support weighted energy bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean#L182-L193
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean#L182-L193

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

theorem OAI.IdealCoprimeBilinearSieve.support_weighted_energy_bound {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ j, (2 : ℝ) ^ (primeSupport (column j)).card * ‖a j‖ ^ 2) ≤
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by sorry
