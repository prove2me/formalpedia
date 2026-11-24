-- Prove2me | Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_diag_multilinear_le
-- name    : GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:53.813363+00:00
-- url     : https://prove2.me/theorems/ab007e12-7f12-489c-8cbe-decb4f1c8d61
-- title:
--   Global Theory: norm iterated FDeriv diag multilinear le
-- statement:
--   The Global Theory construction uses the norm iterated FDeriv diag multilinear le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivMultilinearDiagonalLe.lean#L7-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivMultilinearDiagonalLe.lean#L7-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivMultilinearDiagonalLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ) (i : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => f (fun _ => y)) y‖ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by sorry
