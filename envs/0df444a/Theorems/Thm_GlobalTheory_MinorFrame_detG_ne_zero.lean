-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_detG_ne_zero
-- name    : GlobalTheory.MinorFrame.detG_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:49.885198+00:00
-- url     : https://prove2.me/theorems/6ba650b3-586f-4ad8-90a0-4efa81ce500b
-- title:
--   Minor Frame: det G ne zero
-- statement:
--   The Minor Frame construction uses the det G ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetGNeZero.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetGNeZero.lean#L36-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame
variable {ι : Type}

theorem GlobalTheory.MinorFrame.detG_ne_zero [Fintype ι] (a : ℕ) (n : ι → ℕ) : detG (ι := ι) a n ≠ 0 := by sorry
