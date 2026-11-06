-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_inv_continuousOn_pos
-- name    : OAI.ShortDraftMellin.mobiusExpSum_inv_continuousOn_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:18.270831+00:00
-- url     : https://prove2.me/theorems/38d53356-913f-4af2-871c-44c87c06e2fd
-- title:
--   Short Draft Mellin: mobius Exp Sum inv continuous On pos
-- statement:
--   The Short Draft Mellin construction uses the mobius Exp Sum inv continuous On pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L65-L73
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L65-L73

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

theorem OAI.ShortDraftMellin.mobiusExpSum_inv_continuousOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousOn (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0) := by sorry
