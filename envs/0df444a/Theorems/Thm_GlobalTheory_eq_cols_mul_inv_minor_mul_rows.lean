-- Prove2me | Theorems.Thm_GlobalTheory_eq_cols_mul_inv_minor_mul_rows
-- name    : GlobalTheory.eq_cols_mul_inv_minor_mul_rows
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:36.692393+00:00
-- url     : https://prove2.me/theorems/54efa140-da1b-4d20-9e14-9134b296b8cb
-- title:
--   Global Theory: eq cols mul inv minor mul rows
-- statement:
--   The Global Theory construction uses the eq cols mul inv minor mul rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsColsDetNeZeroOfMul.lean#L7-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsColsDetNeZeroOfMul.lean#L7-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsColsDetNeZeroOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.eq_cols_mul_inv_minor_mul_rows {Ω : Type} [Field Ω] {n r : ℕ}
    (π : Matrix (Fin n) (Fin n) Ω) (hπ : π.rank = r) (ι κ : Fin r → Fin n)
    (hd : (π.submatrix ι κ).det ≠ 0) :
    π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id := by sorry
