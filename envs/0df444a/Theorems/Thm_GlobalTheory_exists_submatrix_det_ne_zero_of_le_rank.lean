-- Prove2me | Theorems.Thm_GlobalTheory_exists_submatrix_det_ne_zero_of_le_rank
-- name    : GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:22.139305+00:00
-- url     : https://prove2.me/theorems/26c54417-81b3-4349-9e52-e46e0302156a
-- title:
--   Global Theory: exists submatrix det ne zero of le rank
-- statement:
--   The Global Theory construction uses the exists submatrix det ne zero of le rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNonzeroMinorOfRank.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNonzeroMinorOfRank.lean#L19-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank :
    ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D,
        (Y.submatrix S τ).det ≠ 0 := by sorry
