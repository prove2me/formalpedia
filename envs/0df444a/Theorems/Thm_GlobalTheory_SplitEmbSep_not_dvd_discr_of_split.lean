-- Prove2me | Theorems.Thm_GlobalTheory_SplitEmbSep_not_dvd_discr_of_split
-- name    : GlobalTheory.SplitEmbSep.not_dvd_discr_of_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:30:25.979727+00:00
-- url     : https://prove2.me/theorems/26526e64-711c-47c1-9b37-eac7dac67c82
-- title:
--   Split Emb Sep: not dvd discr of split
-- statement:
--   The Split Emb Sep construction uses the not dvd discr of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNormSubEqOne.lean#L82-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNormSubEqOne.lean#L82-L125

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

theorem GlobalTheory.SplitEmbSep.not_dvd_discr_of_split {g : ℕ} (hg : g.Prime) (E : Type*) [Field E]
    [NumberField E]
    (h : (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    ¬ (g : ℤ) ∣ discr E := by sorry
