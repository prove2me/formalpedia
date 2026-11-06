-- Prove2me | Theorems.Thm_OAI_SevenEighths_Parameters_compensated_geometry
-- name    : OAI.SevenEighths.Parameters.compensated_geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:59:42.069225+00:00
-- url     : https://prove2.me/theorems/82489e1a-c3f1-491e-b950-41eda7434fc5
-- title:
--   Parameters: compensated geometry
-- statement:
--   The Parameters construction uses the compensated geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Parameters.lean#L12-L26
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Parameters.lean#L12-L26

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_Parameters
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Parameters

theorem OAI.SevenEighths.Parameters.compensated_geometry {d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 := by sorry
