-- Prove2me | Theorems.Thm_GlobalTheory_SplitEmbSep_one_le_norm_intCast
-- name    : GlobalTheory.SplitEmbSep.one_le_norm_intCast
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:11.730808+00:00
-- url     : https://prove2.me/theorems/24303a2e-ce52-4241-bf3b-32e9042fac61
-- title:
--   Split Emb Sep: one le norm int Cast
-- statement:
--   The Split Emb Sep construction uses the one le norm int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNormSubEqOne.lean#L56-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNormSubEqOne.lean#L56-L78

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

theorem GlobalTheory.SplitEmbSep.one_le_norm_intCast {C : Type*} [NormedField C] [IsUltrametricDist C] {g : ℕ}
    (hg : g.Prime) (hgC : ‖(g : C)‖ < 1) {d : ℤ} (hd : ¬ (g : ℤ) ∣ d) : 1 ≤ ‖(d : C)‖ := by sorry
