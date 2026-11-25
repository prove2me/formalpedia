-- Prove2me | Theorems.Thm_GlobalTheory_BigCellUnitary_bigCell_submatrix
-- name    : GlobalTheory.BigCellUnitary.bigCell_submatrix
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:21.24472+00:00
-- url     : https://prove2.me/theorems/4e291cb3-2d30-42da-b304-e6ad09376141
-- title:
--   Big Cell Unitary: big Cell submatrix
-- statement:
--   The Big Cell Unitary construction uses the big Cell submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BigCellMemUnitary.lean#L78-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BigCellMemUnitary.lean#L78-L101

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BigCellMemUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory
open GlobalTheory.BigCellUnitary

theorem GlobalTheory.BigCellUnitary.bigCell_submatrix (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 (diagonal fun a => (star (c a))⁻¹) (diagonal c) 0) 0 0 μ := by sorry
