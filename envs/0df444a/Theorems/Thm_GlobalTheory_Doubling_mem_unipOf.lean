-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_mem_unipOf
-- name    : GlobalTheory.Doubling.mem_unipOf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:03.999271+00:00
-- url     : https://prove2.me/theorems/385de5e1-3104-40b5-833f-72959dd3e1f6
-- title:
--   Doubling: mem unip Of
-- statement:
--   The Doubling construction uses the mem unip Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L429-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L429-L430

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

theorem GlobalTheory.Doubling.mem_unipOf {g : G} : g ∈ unipOf e mat ↔ g ∈ siegelOf e mat ∧ leviMat e (mat g).1 = 1 := by sorry
