-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_submatrix_inj
-- name    : GlobalTheory.Doubling.submatrix_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:26.208804+00:00
-- url     : https://prove2.me/theorems/ca6db402-3633-5689-82dd-74612ca1fa9a
-- title:
--   Doubling: submatrix inj
-- statement:
--   The Doubling construction uses the submatrix inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L33-L34

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
variable (e : m ⊕ n ≃ ι)

theorem GlobalTheory.Doubling.submatrix_inj {M N : Matrix ι ι A} (h : M.submatrix e e = N.submatrix e e) : M = N := by sorry
