-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_pairVec_mem_antiSub
-- name    : GlobalTheory.Doubling.pairVec_mem_antiSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:28.442481+00:00
-- url     : https://prove2.me/theorems/f725b050-029e-4768-899a-ed7aea89f499
-- title:
--   Doubling: pair Vec mem anti Sub
-- statement:
--   The Doubling construction uses the pair Vec mem anti Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L159-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L159-L160

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

theorem GlobalTheory.Doubling.pairVec_mem_antiSub {x y : n → A} : pairVec e x y ∈ antiSub A e ↔ x = -y := by sorry
