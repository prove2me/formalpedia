-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_leviElt_mulVec
-- name    : GlobalTheory.Doubling.leviElt_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:40.403675+00:00
-- url     : https://prove2.me/theorems/10e557ad-6423-474a-9707-5165e0b705c8
-- title:
--   Doubling: levi Elt mul Vec
-- statement:
--   The Doubling construction uses the levi Elt mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L338-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L338-L342

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

theorem GlobalTheory.Doubling.leviElt_mulVec (g : GL n A × GL n A) (x y : n → A) : (leviElt e g).1 *ᵥ pairVec e (x + y) (x - y) =
    pairVec e (g.1.1 *ᵥ x + g.2.1 *ᵥ y) (g.1.1 *ᵥ x - g.2.1 *ᵥ y) := by sorry
