-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_mulLat_le
-- name    : GlobalTheory.SgGlob.mulLat_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:10:43.651106+00:00
-- url     : https://prove2.me/theorems/6f9cbc6b-2619-4524-a57e-f03c9c448264
-- title:
--   Sg Glob: mul Lat le
-- statement:
--   The Sg Glob construction uses the mul Lat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L136-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L136-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
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
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]

theorem GlobalTheory.SgGlob.mulLat_le (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) : mulLat g Λ ≤ Λ := by sorry
