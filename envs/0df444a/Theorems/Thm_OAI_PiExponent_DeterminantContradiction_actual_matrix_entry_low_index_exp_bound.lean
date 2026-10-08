-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_matrix_entry_low_index_exp_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actual_matrix_entry_low_index_exp_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T20:53:34.681983+00:00
-- url     : https://prove2.me/theorems/f6ec3710-bf3e-4f73-839c-ef0769dffc81
-- title:
--   Low-index entry bound for the actual interpolation matrix
-- statement:
--   For every positive height and every row and column of the fixed truncated-log interpolation matrix, the entry is bounded by the low-index exponential rate, with a logarithmic row-count loss. The parent row-sum estimate follows by applying this bound to each selected column and summing over all rows.
-- source:
--   Analytic coefficient sublemma for the fixed determinant family in the irrationality-exponent proof; see https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean

import Definitions.Def_OAI_PiExponent_AnalyticRemainder
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.actual_matrix_entry_low_index_exp_bound
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H)
    (rowIdx : Row d H) (colIdx : Column d H) :
    norm (actualMatrix d H rowIdx colIdx) <=
      Real.exp (H * (d.analyticError + analyticRemainder d H +
        -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) -
        Real.log (actualRowCount d H : Real) / H)) := by sorry
