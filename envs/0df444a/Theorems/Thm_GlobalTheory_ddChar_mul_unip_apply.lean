-- Prove2me | Theorems.Thm_GlobalTheory_ddChar_mul_unip_apply
-- name    : GlobalTheory.ddChar_mul_unip_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:43.448425+00:00
-- url     : https://prove2.me/theorems/13b81d87-3cc7-433f-ae01-7810ee2ce1f0
-- title:
--   Global Theory: dd Char mul unip apply
-- statement:
--   The Global Theory construction uses the dd Char mul unip apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeneralLinearGroupCharEqOneOfDetEqOne.lean#L263-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeneralLinearGroupCharEqOneOfDetEqOne.lean#L263-L269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]

theorem GlobalTheory.ddChar_mul_unip_apply {x y : n → R} (h : y ⬝ᵥ x = 0) (g : GL n R) (i j : n) :
    ((g * ddCharUnip _ (ddChar_vecMulVec_sq h) : GL n R) : Matrix n n R) i j
      = (g : Matrix n n R) i j + (∑ k, (g : Matrix n n R) i k * x k) * y j := by sorry
