-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_norm_le_two
-- name    : OAI.ShortDraftMellin.mobiusExpSum_norm_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:21.543499+00:00
-- url     : https://prove2.me/theorems/b0eaedbf-6a56-49b0-9719-e6e16f94f3c5
-- title:
--   Short Draft Mellin: mobius Exp Sum norm le two
-- statement:
--   The Short Draft Mellin construction uses the mobius Exp Sum norm le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L543-L560
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L543-L560

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin

theorem OAI.ShortDraftMellin.mobiusExpSum_norm_le_two
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖mobiusExpSum χ t‖ ≤ 2 * Real.exp (-t) := by sorry
