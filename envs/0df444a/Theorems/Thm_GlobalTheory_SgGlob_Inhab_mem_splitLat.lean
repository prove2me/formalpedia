-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_splitLat
-- name    : GlobalTheory.SgGlob.Inhab.mem_splitLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:06.999561+00:00
-- url     : https://prove2.me/theorems/489f3a81-5ee2-465d-91a3-1b6a36e02660
-- title:
--   Inhab: mem split Lat
-- statement:
--   The Inhab construction uses the mem split Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L241-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L241-L245

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

theorem GlobalTheory.SgGlob.Inhab.mem_splitLat (v : Fin 8 → E) : v ∈ splitLat E ↔ v 0 ∈ dInv E 1 ∧ v 1 ∈ dOne E ∧
    v 2 ∈ Int' E ∧ v 3 ∈ Int' E ∧ v 4 ∈ Int' E ∧ v 5 ∈ Int' E ∧ v 6 ∈ Int' E ∧ v 7 ∈ Int' E := by sorry
