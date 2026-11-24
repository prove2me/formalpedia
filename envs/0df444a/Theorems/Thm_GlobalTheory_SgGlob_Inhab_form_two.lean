-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_form_two
-- name    : GlobalTheory.SgGlob.Inhab.form_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:29.038466+00:00
-- url     : https://prove2.me/theorems/02649753-98e1-448e-af08-3b129dc41b05
-- title:
--   Inhab: form two
-- statement:
--   The Inhab construction uses the form two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L48-L50

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

theorem GlobalTheory.SgGlob.Inhab.form_two (σ : E →+* E) (v w : Fin 2 → E) :
    form σ !![1, 0; 0, -1] v w = σ (w 0) * v 0 - σ (w 1) * v 1 := by sorry
