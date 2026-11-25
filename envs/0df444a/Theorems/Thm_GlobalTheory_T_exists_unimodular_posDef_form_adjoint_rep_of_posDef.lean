-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unimodular_posDef_form_adjoint_rep_of_posDef
-- name    : GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:28.856361+00:00
-- url     : https://prove2.me/theorems/5fb951b0-cccf-4064-a125-d93792d2b66f
-- title:
--   T: exists unimodular pos Def form adjoint rep of pos Def
-- statement:
--   The T construction uses the exists unimodular pos Def form adjoint rep of pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnimodularPosDefAdjointActionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnimodularPosDefAdjointActionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointActionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m → B0.transpose = B0 → (B0.map (Int.cast : ℤ → ℝ)).PosDef → (∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) → ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧ ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by sorry
