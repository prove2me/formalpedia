-- Prove2me | Theorems.Thm_GlobalTheory_SliceTaylor_norm_padL_le
-- name    : GlobalTheory.SliceTaylor.norm_padL_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:17:47.181467+00:00
-- url     : https://prove2.me/theorems/70714dfb-13cc-4d0d-a52d-a48cffe8be4b
-- title:
--   Slice Taylor: norm pad L le
-- statement:
--   The Slice Taylor construction uses the norm pad L le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivPdLe.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivPdLe.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceTaylor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceTaylor.norm_padL_le {κ κ' : Type} [Fintype κ] [Fintype κ'] (h : κ → V) :
    ‖(padL (κ' := κ') h : κ ⊕ κ' → V)‖ ≤ ‖h‖ := by sorry
