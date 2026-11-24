-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_dInv_zero
-- name    : GlobalTheory.SgGlob.Inhab.mem_dInv_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:42.313973+00:00
-- url     : https://prove2.me/theorems/59f743e4-e4fc-4530-92e3-eb056292da8b
-- title:
--   Inhab: mem d Inv zero
-- statement:
--   The Inhab construction uses the mem d Inv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L27-L29

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

theorem GlobalTheory.SgGlob.Inhab.mem_dInv_zero (x : E) : x ∈ dInv E 0 ↔ x ∈ Int' E := by sorry
