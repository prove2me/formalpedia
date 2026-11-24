-- Prove2me | Theorems.Thm_GlobalTheory_rank_minor_factorisation
-- name    : GlobalTheory.rank_minor_factorisation
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:15:31.950366+00:00
-- url     : https://prove2.me/theorems/ffab458b-ed83-446b-9018-369a36ecf440
-- title:
--   Global Theory: rank minor factorisation
-- statement:
--   The Global Theory construction uses the rank minor factorisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsColsDetNeZeroOfMul.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsColsDetNeZeroOfMul.lean#L73-L82

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

theorem GlobalTheory.rank_minor_factorisation :
    ∀ (Ω : Type) [Field Ω] (n r : ℕ) (π : Matrix (Fin n) (Fin n) Ω), π.rank = r → ∀ ι : Fin r → Fin n, (∀ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 → π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id) ∧ ∀ u : Matrix (Fin n) (Fin r) Ω, π * u = u → (u.submatrix ι id).det ≠ 0 → ∃ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 := by sorry
