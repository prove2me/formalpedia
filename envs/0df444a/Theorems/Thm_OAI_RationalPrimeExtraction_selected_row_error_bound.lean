-- Prove2me | Theorems.Thm_OAI_RationalPrimeExtraction_selected_row_error_bound
-- name    : OAI.RationalPrimeExtraction.selected_row_error_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:27:28.110447+00:00
-- url     : https://prove2.me/theorems/70b6c5cb-e025-435e-b543-9c924ac7796b
-- title:
--   Rational Prime Extraction: selected row error bound
-- statement:
--   The Rational Prime Extraction construction uses the selected row error bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L264-L271
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L264-L271

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

theorem OAI.RationalPrimeExtraction.selected_row_error_bound (D : ℕ) (hD : 1 ≤ D)
    (r : ℕ) (hr : r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ))) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by sorry
