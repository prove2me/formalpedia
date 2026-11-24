-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_leviElt_anti
-- name    : GlobalTheory.Doubling.leviElt_anti
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:28.162983+00:00
-- url     : https://prove2.me/theorems/41aef4f6-5942-45d6-ad89-289936053670
-- title:
--   Doubling: levi Elt anti
-- statement:
--   The Doubling construction uses the levi Elt anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L348-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L348-L350

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

theorem GlobalTheory.Doubling.leviElt_anti (g : GL n A × GL n A) (y : n → A) :
    (leviElt e g).1 *ᵥ pairVec e y (-y) = pairVec e (g.2.1 *ᵥ y) (-(g.2.1 *ᵥ y)) := by sorry
