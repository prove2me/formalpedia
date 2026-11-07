-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_compact_paperRadialFourier_regular
-- name    : OAI.EisensteinSchwartzPoisson.compact_paperRadialFourier_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:07.019365+00:00
-- url     : https://prove2.me/theorems/01241318-f3ed-488e-8984-ba540d0288cb
-- title:
--   Eisenstein Schwartz Poisson: compact paper Radial Fourier regular
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the compact paper Radial Fourier regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/RadialFourier.lean#L424-L431
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/RadialFourier.lean#L424-L431

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory
open scoped SchwartzMap ContDiff

theorem OAI.EisensteinSchwartzPoisson.compact_paperRadialFourier_regular
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (A K : ℕ) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) ∧
      ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by sorry
