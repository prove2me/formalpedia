-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeathBrownIteration_step_sub
-- name    : OAI.SevenEighths.HeathBrownIteration.step_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:59.55336+00:00
-- url     : https://prove2.me/theorems/9b641d3b-45cf-40a2-a5a6-9d8f72f21dac
-- title:
--   Heath Brown Iteration: step sub
-- statement:
--   The Heath Brown Iteration construction uses the step sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/HeathBrownIteration.lean#L16-L22
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/HeathBrownIteration.lean#L16-L22

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_HeathBrownIteration
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.HeathBrownIteration
noncomputable section

theorem OAI.SevenEighths.HeathBrownIteration.step_sub (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by sorry
