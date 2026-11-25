-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_RowIrr_rowSub_one
-- name    : GlobalTheory.MinorFrame.RowIrr.rowSub_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:29.341318+00:00
-- url     : https://prove2.me/theorems/c426c041-ee87-44c7-979e-2b649e038651
-- title:
--   Row Irr: row Sub one
-- statement:
--   The Row Irr construction uses the row Sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean#L51-L60

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

theorem GlobalTheory.MinorFrame.RowIrr.rowSub_one {d a : ℕ} (P : Pol ι d a) : rowSub (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) P = P := by sorry
