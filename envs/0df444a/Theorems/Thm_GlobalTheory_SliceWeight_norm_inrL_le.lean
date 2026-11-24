-- Prove2me | Theorems.Thm_GlobalTheory_SliceWeight_norm_inrL_le
-- name    : GlobalTheory.SliceWeight.norm_inrL_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:17:30.188122+00:00
-- url     : https://prove2.me/theorems/9f3a2a17-c616-4f42-b17d-a9f0906d1d1e
-- title:
--   Slice Weight: norm inr L le
-- statement:
--   The Slice Weight construction uses the norm inr L le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowNormMulSeminormSliceRLe.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowNormMulSeminormSliceRLe.lean#L13-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
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
open GlobalTheory GlobalTheory.SliceWeight
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceWeight.norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] : ‖(inrL (V := V) κ κ')‖ ≤ 1 := by sorry
