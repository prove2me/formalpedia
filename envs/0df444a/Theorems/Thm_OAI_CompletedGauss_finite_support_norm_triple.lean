-- Prove2me | Theorems.Thm_OAI_CompletedGauss_finite_support_norm_triple
-- name    : OAI.CompletedGauss.finite_support_norm_triple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:53.751201+00:00
-- url     : https://prove2.me/theorems/1d947b68-9cec-49ff-916b-72505bc94597
-- title:
--   Completed Gauss: finite support norm triple
-- statement:
--   The Completed Gauss construction uses the finite support norm triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/IdealMobius.lean#L356-L381
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/IdealMobius.lean#L356-L381

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
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
open OAI.CompletedGauss
open ActualEisensteinCubic
open ActualEisensteinCubic

theorem OAI.CompletedGauss.finite_support_norm_triple (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (F : Ideal O × Ideal O × Ideal O → ℂ)
    (hzero : ∀ I J H, I = 0 ∨ J = 0 ∨ H = 0 → F (I, J, H) = 0)
    (hwindow : ∀ I J H,
      W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
        (Ideal.absNorm H : ℝ) ^ 3 / X) = 0 → F (I, J, H) = 0) :
    (Function.support F).Finite := by sorry
