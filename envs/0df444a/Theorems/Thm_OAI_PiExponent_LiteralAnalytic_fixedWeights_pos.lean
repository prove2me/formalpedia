-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_fixedWeights_pos
-- name    : OAI.PiExponent.LiteralAnalytic.fixedWeights_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T10:02:19.361473+00:00
-- url     : https://prove2.me/theorems/4b7b967c-b7aa-4be4-8af1-f5c306c956e1
-- title:
--   Positivity of fixed logarithmic weights
-- statement:
--   Every fixed logarithmic weight associated with admissible data is strictly positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L133-L153

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.LiteralAnalytic.fixedWeights_pos {nu : ℝ}
    (d : FixedData nu) (i : Fin d.m) : 0 < fixedWeights d i := by
  sorry
