-- Prove2me | Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_mul
-- name    : GlobalTheory.BlockValue.OnlyIn.mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:23.217639+00:00
-- url     : https://prove2.me/theorems/1d8c141a-3347-4b66-bed0-1cdb4e8283cd
-- title:
--   Only In: mul
-- statement:
--   The Only In construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L22-L32

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

theorem GlobalTheory.BlockValue.OnlyIn.mul {S : σ → Prop} {f g : MvPowerSeries σ C} (hf : OnlyIn S f) (hg : OnlyIn S g) :
    OnlyIn S (f * g) := by sorry
