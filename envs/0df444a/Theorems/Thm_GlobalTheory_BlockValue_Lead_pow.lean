-- Prove2me | Theorems.Thm_GlobalTheory_BlockValue_Lead_pow
-- name    : GlobalTheory.BlockValue.Lead.pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:45.988415+00:00
-- url     : https://prove2.me/theorems/0e4da1fd-a01d-411f-8f02-e93210ec970b
-- title:
--   Lead: pow
-- statement:
--   The Lead construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L104-L108

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}

theorem GlobalTheory.BlockValue.Lead.pow {π : σ → κ} {d : σ →₀ ℕ} {f : MvPowerSeries σ C} (hf : Lead π d f) (k : ℕ) :
    Lead π (k • d) (f ^ k) := by sorry
