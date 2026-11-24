-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_dInv
-- name    : GlobalTheory.SgGlob.Inhab.map_mem_dInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:44.519323+00:00
-- url     : https://prove2.me/theorems/bc8711c0-e57c-4569-8daf-bb931737dfa6
-- title:
--   Inhab: map mem d Inv
-- statement:
--   The Inhab construction uses the map mem d Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L192-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L192-L203

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

theorem GlobalTheory.SgGlob.Inhab.map_mem_dInv (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {x : E} (hx : x ∈ dInv E 1) :
    σ x ∈ dInv E 1 := by sorry
