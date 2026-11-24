-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_iteratedFDeriv_multilinear_diagonal_le
-- name    : GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:56:49.49873+00:00
-- url     : https://prove2.me/theorems/2940d212-a674-4107-a1b1-ba43ec79de50
-- title:
--   T: norm iterated FDeriv multilinear diagonal le
-- statement:
--   The T construction uses the norm iterated FDeriv multilinear diagonal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivMultilinearDiagonalLeStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivMultilinearDiagonalLeStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivMultilinearDiagonalLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivMultilinearDiagonalLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ) (i : ℕ) (y : E),
    ‖iteratedFDeriv ℝ i (fun y : E => f (fun _ => y)) y‖ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by sorry
