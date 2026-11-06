-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_continuousOn_pos
-- name    : OAI.ShortDraftMellin.mobiusExpSum_continuousOn_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:17.524208+00:00
-- url     : https://prove2.me/theorems/dd927439-934b-4384-b7bf-43b52cb571ff
-- title:
--   Short Draft Mellin: mobius Exp Sum continuous On pos
-- statement:
--   The Short Draft Mellin construction uses the mobius Exp Sum continuous On pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L13-L63
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L13-L63

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin

theorem OAI.ShortDraftMellin.mobiusExpSum_continuousOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousOn (mobiusExpSum χ) (Set.Ioi (0 : ℝ)) := by sorry
