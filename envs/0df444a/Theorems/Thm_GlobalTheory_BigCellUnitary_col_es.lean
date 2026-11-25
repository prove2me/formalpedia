-- Prove2me | Theorems.Thm_GlobalTheory_BigCellUnitary_col_es
-- name    : GlobalTheory.BigCellUnitary.col_es
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:54.645997+00:00
-- url     : https://prove2.me/theorems/4e8a0246-38b1-51e3-bdad-4fd2c9c9e9ed
-- title:
--   Big Cell Unitary: col es
-- statement:
--   The Big Cell Unitary construction uses the col es property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BigCellMemUnitary.lean#L65-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BigCellMemUnitary.lean#L65-L76

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

theorem GlobalTheory.BigCellUnitary.col_es (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (esI k r b) = if i.val = b.val then (star (c b))⁻¹ else 0 := by sorry
