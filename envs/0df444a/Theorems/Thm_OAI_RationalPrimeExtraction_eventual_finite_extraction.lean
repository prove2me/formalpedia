-- Prove2me | Theorems.Thm_OAI_RationalPrimeExtraction_eventual_finite_extraction
-- name    : OAI.RationalPrimeExtraction.eventual_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:27:25.482122+00:00
-- url     : https://prove2.me/theorems/6d5fa685-5a8c-4ea9-883b-56d4eedccc00
-- title:
--   Rational Prime Extraction: eventual finite extraction
-- statement:
--   The Rational Prime Extraction construction uses the eventual finite extraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L279-L328
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L279-L328

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
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.RationalPrimeExtraction

theorem OAI.RationalPrimeExtraction.eventual_finite_extraction (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ A : O → ℂ,
      (∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
        ‖A 1 - A ((r : O) ^ 6)‖ ≤
          512 * (D : ℝ) ^ (41 / 45 : ℝ)) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤
          (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖A 1‖ ≤ 1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by sorry
