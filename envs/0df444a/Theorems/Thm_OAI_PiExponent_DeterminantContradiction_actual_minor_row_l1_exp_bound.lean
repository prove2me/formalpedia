-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_row_l1_exp_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actual_minor_row_l1_exp_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T19:48:29.109172+00:00
-- url     : https://prove2.me/theorems/5b9ab31c-d24b-4336-adec-68429fdf66ff
-- title:
--   Uniform exponential bound for each actual minor row sum
-- statement:
--   Fix an admissible family $d$, a nonnegative exponent $\\nu$, a positive height $H$, a column selection, and a row of the selected minor. The sum of the absolute values of the entries in that row is at most
--
--   $$\\exp(H C_d(H)),$$
--
--   where $C_d(H)$ is the analytic error plus the explicit remainder and the larger of the collision and low-index exponents in the parent determinant estimate. This uniform row bound supplies the analytic input for the determinant reduction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean

import Definitions.Def_OAI_PiExponent_AnalyticRemainder
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_row_l1_exp_bound
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H) (selection : Row d H -> Column d H)
    (rowIdx : Row d H) :
    Finset.sum Finset.univ (fun colIdx : Row d H =>
      norm ((actualMinor d H selection) rowIdx colIdx)) <=
      Real.exp (H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)))) := by sorry
