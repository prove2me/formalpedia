-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_inv_locallyIntegrableOn_pos
-- name    : OAI.ShortDraftMellin.mobiusExpSum_inv_locallyIntegrableOn_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:09.501127+00:00
-- url     : https://prove2.me/theorems/66e16af3-230f-49b7-9152-41132ca9cdf3
-- title:
--   Short Draft Mellin: mobius Exp Sum inv locally Integrable On pos
-- statement:
--   The Short Draft Mellin construction uses the mobius Exp Sum inv locally Integrable On pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L75-L79
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L75-L79

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

theorem OAI.ShortDraftMellin.mobiusExpSum_inv_locallyIntegrableOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn
      (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0) := by sorry
