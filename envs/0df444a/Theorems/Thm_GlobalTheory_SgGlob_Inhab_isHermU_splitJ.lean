-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_isHermU_splitJ
-- name    : GlobalTheory.SgGlob.Inhab.isHermU_splitJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:39.212436+00:00
-- url     : https://prove2.me/theorems/2f676293-ae8d-4a92-9051-8074ff9c64dd
-- title:
--   Inhab: is Herm U split J
-- statement:
--   The Inhab construction uses the is Herm U split J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L224-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L224-L229

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

theorem GlobalTheory.SgGlob.Inhab.isHermU_splitJ (σ : E →+* E) : IsHermU σ (splitJ E) := by sorry
