-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_val_aOf
-- name    : GlobalTheory.Doubling.val_aOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:39.739894+00:00
-- url     : https://prove2.me/theorems/2ef6a49f-7bc4-4b59-98b5-b228114c7207
-- title:
--   Doubling: val a Of
-- statement:
--   The Doubling construction uses the val a Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L427-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L427-L427

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

theorem GlobalTheory.Doubling.val_aOf (p : siegelOf e mat) : (aOf e mat p).1 = (leviMat e (mat p).1).det := by sorry

attribute [defeq] GlobalTheory.Doubling.val_aOf
