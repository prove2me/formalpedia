-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeathBrownIteration_step_error_le
-- name    : OAI.SevenEighths.HeathBrownIteration.step_error_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:44:04.378206+00:00
-- url     : https://prove2.me/theorems/1a050797-ed81-4852-978b-33050b2d7a34
-- title:
--   Heath Brown Iteration: step error le
-- statement:
--   The Heath Brown Iteration construction uses the step error le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/HeathBrownIteration.lean#L31-L35
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/HeathBrownIteration.lean#L31-L35

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

theorem OAI.SevenEighths.HeathBrownIteration.step_error_le {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by sorry
