-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_two_regime_decay
-- name    : OAI.EisensteinSchwartzPoisson.two_regime_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:44:33.213123+00:00
-- url     : https://prove2.me/theorems/10d30659-3f1b-4bec-9266-593a6049d844
-- title:
--   Eisenstein Schwartz Poisson: two regime decay
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the two regime decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/QuadraticProfiles.lean#L251-L273
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/QuadraticProfiles.lean#L251-L273

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_QuadraticProfiles
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
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound

theorem OAI.EisensteinSchwartzPoisson.two_regime_decay (A : ℕ) (f B₀ B₁ M N : ℝ)
    (_hf : 0 ≤ f) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hM : 0 < M) (hN : 0 < N)
    (hsmall : f ≤ B₀) (hlarge : N ≤ M → f ≤ B₁ * (N / M) ^ A) :
    f ≤ (2 : ℝ) ^ A * (B₀ + B₁) / (1 + M / N) ^ A := by sorry
