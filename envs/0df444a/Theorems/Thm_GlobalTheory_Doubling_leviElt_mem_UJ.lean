-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_leviElt_mem_UJ
-- name    : GlobalTheory.Doubling.leviElt_mem_UJ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:36.235146+00:00
-- url     : https://prove2.me/theorems/642776a8-4773-4cf5-bc35-c76597a21445
-- title:
--   Doubling: levi Elt mem UJ
-- statement:
--   The Doubling construction uses the levi Elt mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L371-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L371-L390

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
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
variable [Invertible (2 : A)]

theorem GlobalTheory.Doubling.leviElt_mem_UJ {σ : A →+* A} {J : Matrix n n A} {α β : GL n A} (h1 : cT σ β.1 * J * α.1 = J)
    (h2 : cT σ α.1 * J * β.1 = J) : leviElt e (α, β) ∈ UJ σ (dblGram e J) := by sorry
