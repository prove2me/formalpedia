-- Prove2me | Theorems.Thm_OAI_RationalPrimeExtraction_eventual_count_power
-- name    : OAI.RationalPrimeExtraction.eventual_count_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:27:22.164185+00:00
-- url     : https://prove2.me/theorems/18c7f74f-58ff-4753-bb6e-0d7b3b35e631
-- title:
--   Rational Prime Extraction: eventual count power
-- statement:
--   The Rational Prime Extraction construction uses the eventual count power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L203-L219
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L203-L219

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
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
open OAI.RationalPrimeExtraction

theorem OAI.RationalPrimeExtraction.eventual_count_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      2 ≤ D ∧
      (D : ℝ) ^ ((4 / 45 : ℝ) - ε) ≤
        ((selected ((D : ℝ) ^ (4 / 45 : ℝ))).card : ℝ) := by sorry
