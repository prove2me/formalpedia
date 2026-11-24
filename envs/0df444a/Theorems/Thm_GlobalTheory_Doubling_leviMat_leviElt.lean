-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_leviMat_leviElt
-- name    : GlobalTheory.Doubling.leviMat_leviElt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:34.457672+00:00
-- url     : https://prove2.me/theorems/e5fbfe3f-03e9-46c2-8c23-3f7d309663a0
-- title:
--   Doubling: levi Mat levi Elt
-- statement:
--   The Doubling construction uses the levi Mat levi Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L365-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L365-L369

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

theorem GlobalTheory.Doubling.leviMat_leviElt (g : GL n A × GL n A) : leviMat e (leviElt e g).1 = g.1.1 := by sorry
