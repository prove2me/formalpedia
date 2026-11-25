-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_RowIrr_topMinors_ne_zero
-- name    : GlobalTheory.MinorFrame.RowIrr.topMinors_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:39.009102+00:00
-- url     : https://prove2.me/theorems/0c293e3e-31db-4670-a32e-c012c7db3a71
-- title:
--   Row Irr: top Minors ne zero
-- statement:
--   The Row Irr construction uses the top Minors ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean#L71-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EvalBasePtTopMinors
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
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RowIrr
open GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.RowIrr.topMinors_ne_zero {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : topMinors (ι := ι) h n ≠ 0 := by sorry
