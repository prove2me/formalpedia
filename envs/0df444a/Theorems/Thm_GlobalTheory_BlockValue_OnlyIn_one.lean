-- Prove2me | Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_one
-- name    : GlobalTheory.BlockValue.OnlyIn.one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:55.51964+00:00
-- url     : https://prove2.me/theorems/14029a67-be7c-4b22-8945-707649811e1c
-- title:
--   Only In: one
-- statement:
--   The Only In construction uses the one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L15-L20

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

theorem GlobalTheory.BlockValue.OnlyIn.one (S : σ → Prop) : OnlyIn S (1 : MvPowerSeries σ C) := by sorry
