-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_RowIrr_rowSub_rowSub
-- name    : GlobalTheory.MinorFrame.RowIrr.rowSub_rowSub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:35.093672+00:00
-- url     : https://prove2.me/theorems/9b8f5610-b1b2-5b25-ba76-9e9b2ec1efc2
-- title:
--   Row Irr: row Sub row Sub
-- statement:
--   The Row Irr construction uses the row Sub row Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean#L39-L49

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

theorem GlobalTheory.MinorFrame.RowIrr.rowSub_rowSub {d a : ℕ} (κ κ' : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rowSub κ (rowSub κ' P) = rowSub (fun τ => κ τ * κ' τ) P := by sorry
