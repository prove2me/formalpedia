-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_schwartzCLM_family_finite_seminorm_control
-- name    : OAI.EisensteinSchwartzPoisson.schwartzCLM_family_finite_seminorm_control
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:27.942025+00:00
-- url     : https://prove2.me/theorems/ea866743-4f60-4e39-af1d-c67bcd7e0ea0
-- title:
--   Eisenstein Schwartz Poisson: schwartz CLM family finite seminorm control
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the schwartz CLM family finite seminorm control property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/RadialFourier.lean#L356-L390
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/RadialFourier.lean#L356-L390

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

theorem OAI.EisensteinSchwartzPoisson.schwartzCLM_family_finite_seminorm_control
    (T : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K →
        SchwartzMap.seminorm ℝ 0 0 (T j W) +
          SchwartzMap.seminorm ℝ (2 * A) 0 (T j W) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by sorry
