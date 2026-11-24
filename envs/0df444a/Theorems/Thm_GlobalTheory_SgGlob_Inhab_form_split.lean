-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_form_split
-- name    : GlobalTheory.SgGlob.Inhab.form_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:33.214174+00:00
-- url     : https://prove2.me/theorems/f0d476be-bc1e-414c-8739-bbf6adbb4788
-- title:
--   Inhab: form split
-- statement:
--   The Inhab construction uses the form split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L232-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L232-L235

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
omit [NumberField E]

theorem GlobalTheory.SgGlob.Inhab.form_split (σ : E →+* E) (v w : Fin 8 → E) :
    form σ (splitJ E) v w = σ (w 0) * v 1 + σ (w 1) * v 0 + σ (w 2) * v 2 + σ (w 3) * v 3 +
      σ (w 4) * v 4 + σ (w 5) * v 5 + σ (w 6) * v 6 - σ (w 7) * v 7 := by sorry
