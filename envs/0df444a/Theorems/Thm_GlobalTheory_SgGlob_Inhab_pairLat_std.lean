-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_pairLat_std
-- name    : GlobalTheory.SgGlob.Inhab.pairLat_std
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:46.085958+00:00
-- url     : https://prove2.me/theorems/47996169-16be-4a17-973a-fffc94a725e0
-- title:
--   Inhab: pair Lat std
-- statement:
--   The Inhab construction uses the pair Lat std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L74-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.SgGlob.Inhab.pairLat_std {g : ℕ} (hg : g ≠ 0) :
    pairLat (r := 0) g (!![0; 1] : Matrix (Fin 2) (Fin (0 + 1)) E) !![(g : E); 1 + g] = std E := by sorry
