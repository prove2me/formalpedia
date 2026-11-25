-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_linearIndependent_rat_basis_adapted_subspace
-- name    : GlobalTheory.T.exists_linearIndependent_rat_basis_adapted_subspace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:20.863632+00:00
-- url     : https://prove2.me/theorems/de6d455d-f035-4934-8d20-c81db3604cc3
-- title:
--   T: exists linear Independent rat basis adapted subspace
-- statement:
--   The T construction uses the exists linear Independent rat basis adapted subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLinearIndependentRatBasisAdaptedSubspaceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLinearIndependentRatBasisAdaptedSubspaceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLinearIndependentRatBasisAdaptedSubspace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLinearIndependentRatBasisAdaptedSubspaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_linearIndependent_rat_basis_adapted_subspace : ∀ (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)), I ≤ L → Module.finrank ℚ L = g → ∃ rk : ℕ, rk ≤ g ∧ ∃ ε : Fin g → Fin r → ℚ, LinearIndependent ℚ ε ∧ (∀ i, ε i ∈ L) ∧ (∀ i : Fin g, i.val < rk → ε i ∈ I) ∧ ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i | i.val < rk}) := by sorry
