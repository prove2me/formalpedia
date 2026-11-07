-- Prove2me | Theorems.Thm_OAI_QuadraticSquarefreeKernel_quadraticRow_primary_tsum_decomposition
-- name    : OAI.QuadraticSquarefreeKernel.quadraticRow_primary_tsum_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:29.103251+00:00
-- url     : https://prove2.me/theorems/8c0e69c8-4b58-4f70-a168-f6314ca12739
-- title:
--   Quadratic Squarefree Kernel: quadratic Row primary tsum decomposition
-- statement:
--   The Quadratic Squarefree Kernel construction uses the quadratic Row primary tsum decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CubeLabels.lean#L433-L449
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/CubeLabels.lean#L433-L449

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeLabels
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
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open OAI.QuadraticSquarefreeKernel
open ActualEisensteinCubic QuadraticInitialBound CompletedGauss

theorem OAI.QuadraticSquarefreeKernel.quadraticRow_primary_tsum_decomposition {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : {I : Ideal O // I ≠ 0},
      quadraticRow P hg S (primaryGenerator I.val) * W ((Ideal.absNorm I.val : ℝ) / X)) =
    ∑' p : {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D},
      rowCoprimeMask P S (primaryGenerator p.1.val) *
      quadraticRow P hg S (primaryGenerator p.2.val) *
      W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * Ideal.absNorm p.2.val) / X) := by sorry
