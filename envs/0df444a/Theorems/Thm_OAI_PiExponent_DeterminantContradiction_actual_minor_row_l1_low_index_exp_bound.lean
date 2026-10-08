-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_row_l1_low_index_exp_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actual_minor_row_l1_low_index_exp_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T19:59:25.194063+00:00
-- url     : https://prove2.me/theorems/502ab8da-19a2-43e2-82ab-42ca7cef209e
-- title:
--   Low index branch for the actual minor row sum
-- statement:
--   For each row of the selected minor, the sum of absolute values is at most the exponential low index branch. This is the alternative obtained when fewer rows lie below the weight cutoff, forcing a lower bound on total row weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean

import Definitions.Def_OAI_PiExponent_AnalyticRemainder
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_row_l1_low_index_exp_bound
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H) (selection : Row d H -> Column d H)
    (rowIdx : Row d H) :
    Finset.sum Finset.univ (fun colIdx : Row d H =>
      norm ((actualMinor d H selection) rowIdx colIdx)) <=
      Real.exp (H * (d.analyticError + analyticRemainder d H +
        -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H))) := by sorry
