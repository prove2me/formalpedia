-- Prove2me | Theorems.Thm_GlobalTheory_UpqChar_det_conj_rect
-- name    : GlobalTheory.UpqChar.det_conj_rect
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:48.17946+00:00
-- url     : https://prove2.me/theorems/758c7856-8f4e-44df-a69a-cec032541db1
-- title:
--   Upq Char: det conj rect
-- statement:
--   The Upq Char construction uses the det conj rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryPQContinuousCharacterEqDetPowProd.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryPQContinuousCharacterEqDetPowProd.lean#L8-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryPQContinuousCharacterEqDetPowProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.UpqChar

theorem GlobalTheory.UpqChar.det_conj_rect {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ ℂ) (B' : Matrix κ ι ℂ) (h1 : B * B' = 1) (h2 : B' * B = 1)
    (M : Matrix κ κ ℂ) : (B * M * B').det = M.det := by sorry
