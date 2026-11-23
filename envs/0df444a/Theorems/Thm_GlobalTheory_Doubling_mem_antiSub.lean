-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_mem_antiSub
-- name    : GlobalTheory.Doubling.mem_antiSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:49.255327+00:00
-- url     : https://prove2.me/theorems/436ee8f6-2e68-4e3d-963d-fbfad2866df0
-- title:
--   Doubling: mem anti Sub
-- statement:
--   The Doubling construction uses the mem anti Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L168-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L168-L173

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)

theorem GlobalTheory.Doubling.mem_antiSub {w : ι → A} : w ∈ antiSub A e ↔ ∃ x, w = pairVec e x (-x) := by sorry
