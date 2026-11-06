-- Prove2me | Theorems.Thm_OAI_RationalPrimeExtraction_lower_count_and_extract
-- name    : OAI.RationalPrimeExtraction.lower_count_and_extract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:49:33.246923+00:00
-- url     : https://prove2.me/theorems/338ae8df-e8de-4e33-ae03-f99c786a08c0
-- title:
--   Rational Prime Extraction: lower count and extract
-- statement:
--   The Rational Prime Extraction construction uses the lower count and extract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L278-L298
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L278-L298

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
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
open OAI.RationalPrimeExtraction

theorem OAI.RationalPrimeExtraction.lower_count_and_extract
    [DecidableEq O] (A : O → ℂ) (rows : Finset O) (E B : ℝ) (hE : 0 ≤ E) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (selected Y).image (fun r : ℕ => (r : O) ^ 6) ⊆ rows →
      (∀ r ∈ selected Y, ‖A 1 - A ((r : O) ^ 6)‖ ≤ E) →
      (∑ u ∈ rows, ‖A u‖ ^ 2) ≤ B →
      (Real.log 2 / 20) * (Y / Real.log Y) * ‖A 1‖ ^ 2 ≤
        2 * B + 2 * ((selected Y).card : ℝ) * E ^ 2 := by sorry
