-- Prove2me | Theorems.Thm_OAI_RationalPrimeExtraction_selected_rows_in_ball
-- name    : OAI.RationalPrimeExtraction.selected_rows_in_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:27:31.081171+00:00
-- url     : https://prove2.me/theorems/3ba44d77-5840-4e21-9720-d68ea0d48464
-- title:
--   Rational Prime Extraction: selected rows in ball
-- statement:
--   The Rational Prime Extraction construction uses the selected rows in ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L221-L262
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L221-L262

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

theorem OAI.RationalPrimeExtraction.selected_rows_in_ball [DecidableEq O] (D : ℕ) (hD : 1 ≤ D) :
    (selected ((D : ℝ) ^ (4 / 45 : ℝ))).image
      (fun r : ℕ => (r : O) ^ 6) ⊆
      rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ := by sorry
