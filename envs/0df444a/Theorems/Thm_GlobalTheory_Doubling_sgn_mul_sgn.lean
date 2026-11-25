-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_sgn_mul_sgn
-- name    : GlobalTheory.Doubling.sgn_mul_sgn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:05.397535+00:00
-- url     : https://prove2.me/theorems/4c421ef4-779f-461c-b8ff-f67fa3e0be73
-- title:
--   Doubling: sgn mul sgn
-- statement:
--   The Doubling construction uses the sgn mul sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L306-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L306-L307

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
variable [Fintype n] [Fintype ι]
variable {e}
variable [DecidableEq n] [DecidableEq ι]
variable (e)

theorem GlobalTheory.Doubling.sgn_mul_sgn : blkMat e (1 : Matrix n n A) (-1) * blkMat e (1 : Matrix n n A) (-1) = 1 := by sorry
