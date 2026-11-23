-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_leviElt_diag
-- name    : GlobalTheory.Doubling.leviElt_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:32.186557+00:00
-- url     : https://prove2.me/theorems/ce54b69a-2cfd-490f-ba82-01612ad4ee7f
-- title:
--   Doubling: levi Elt diag
-- statement:
--   The Doubling construction uses the levi Elt diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L344-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L344-L346

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

theorem GlobalTheory.Doubling.leviElt_diag (g : GL n A × GL n A) (x : n → A) :
    (leviElt e g).1 *ᵥ pairVec e x x = pairVec e (g.1.1 *ᵥ x) (g.1.1 *ᵥ x) := by sorry
