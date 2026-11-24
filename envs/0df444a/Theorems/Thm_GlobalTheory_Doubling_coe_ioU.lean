-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_coe_ioU
-- name    : GlobalTheory.Doubling.coe_ioU
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:13.499198+00:00
-- url     : https://prove2.me/theorems/4c87da05-e38f-40f8-8424-07faffc22b17
-- title:
--   Doubling: coe io U
-- statement:
--   The Doubling construction uses the coe io U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L527-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L527-L528

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
variable [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι] (σ : A →+* A)

theorem GlobalTheory.Doubling.coe_ioU (e : n ⊕ n ≃ ι) {J : Matrix n n A} {Q : Matrix ι ι A} (h : Q = dblGram e J) (g : UJ σ J × UJ σ J) :
    (ioU σ e h g : GL ι A) = blkGL e (g.1, g.2) := by sorry
