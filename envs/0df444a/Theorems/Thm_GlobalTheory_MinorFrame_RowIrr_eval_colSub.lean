-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_RowIrr_eval_colSub
-- name    : GlobalTheory.MinorFrame.RowIrr.eval_colSub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:50.610468+00:00
-- url     : https://prove2.me/theorems/b5f4e02d-8842-59c5-a9c2-906716c2f399
-- title:
--   Row Irr: eval col Sub
-- statement:
--   The Row Irr construction uses the eval col Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EvalBasePtTopMinors.lean#L32-L37

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

theorem GlobalTheory.MinorFrame.RowIrr.eval_colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (z : Var ι d a → ℂ) (P : Pol ι d a) :
    eval z (colSub g P) = eval (fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * z (y.1, y.2.1, j')) P := by sorry
