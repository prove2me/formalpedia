-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_mem_diagSub
-- name    : GlobalTheory.Doubling.mem_diagSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:41.283851+00:00
-- url     : https://prove2.me/theorems/f7ccfb4e-e68c-4ddd-a4a1-9c9da6a79c37
-- title:
--   Doubling: mem diag Sub
-- statement:
--   The Doubling construction uses the mem diag Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L162-L166

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

theorem GlobalTheory.Doubling.mem_diagSub {w : ι → A} : w ∈ diagSub A e ↔ ∃ x, w = pairVec e x x := by sorry
