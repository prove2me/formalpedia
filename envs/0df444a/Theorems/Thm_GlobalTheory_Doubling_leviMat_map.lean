-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_leviMat_map
-- name    : GlobalTheory.Doubling.leviMat_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:42.260954+00:00
-- url     : https://prove2.me/theorems/d18877f3-1e92-4ae4-aa6e-5d6475744905
-- title:
--   Doubling: levi Mat map
-- statement:
--   The Doubling construction uses the levi Mat map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L202-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L202-L203

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

theorem GlobalTheory.Doubling.leviMat_map (f : A →+* B) (M : Matrix ι ι A) : leviMat e (M.map f) = (leviMat e M).map f := by sorry
