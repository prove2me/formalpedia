-- Prove2me | Theorems.Thm_GlobalTheory_SplitEmbSep_norm_det_lt_one
-- name    : GlobalTheory.SplitEmbSep.norm_det_lt_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:10.98582+00:00
-- url     : https://prove2.me/theorems/190c999d-b3f1-4a80-a13c-a2e740ff57bb
-- title:
--   Split Emb Sep: norm det lt one
-- statement:
--   The Split Emb Sep construction uses the norm det lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNormSubEqOne.lean#L39-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNormSubEqOne.lean#L39-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNormSubEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SplitEmbSep
open NumberField

theorem GlobalTheory.SplitEmbSep.norm_det_lt_one {C ι : Type*} [NormedField C] [IsUltrametricDist C]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C) (hM : ∀ i j, ‖M i j‖ ≤ 1) (k : ι)
    (hk : ∀ i, ‖M i k‖ < 1) : ‖M.det‖ < 1 := by sorry
