-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- name    : GlobalTheory.Doubling.val_leviOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:51.633737+00:00
-- url     : https://prove2.me/theorems/a223893a-105e-46eb-b8cb-ef8d988509e4
-- title:
--   Doubling: val levi Of
-- statement:
--   The Doubling construction uses the val levi Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L426-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L426-L426

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
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A)
variable {e mat}

theorem GlobalTheory.Doubling.val_leviOf (p : siegelOf e mat) : (leviOf e mat p).1 = leviMat e (mat p).1 := by sorry

attribute [defeq] GlobalTheory.Doubling.val_leviOf
