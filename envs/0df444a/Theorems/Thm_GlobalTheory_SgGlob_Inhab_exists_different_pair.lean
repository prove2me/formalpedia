-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_exists_different_pair
-- name    : GlobalTheory.SgGlob.Inhab.exists_different_pair
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:37.708592+00:00
-- url     : https://prove2.me/theorems/8d478134-5f8e-4504-9a16-9b4b8466089d
-- title:
--   Inhab: exists different pair
-- statement:
--   The Inhab construction uses the exists different pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L408-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L408-L413

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

theorem GlobalTheory.SgGlob.Inhab.exists_different_pair (E : Type) [Field E] [NumberField E] :
    ∃ a b : 𝓞 E, a ≠ 0 ∧ differentIdeal ℤ (𝓞 E) = Ideal.span {a, b} := by sorry
