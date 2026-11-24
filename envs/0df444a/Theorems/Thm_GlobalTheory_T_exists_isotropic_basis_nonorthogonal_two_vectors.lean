-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isotropic_basis_nonorthogonal_two_vectors
-- name    : GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:05.310497+00:00
-- url     : https://prove2.me/theorems/b6ee911f-492c-40d0-8b20-9d66cbf5dc54
-- title:
--   T: exists isotropic basis nonorthogonal two vectors
-- statement:
--   The T construction uses the exists isotropic basis nonorthogonal two vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicBasisNonorthogonalTwoVectorsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicBasisNonorthogonalTwoVectorsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 → ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧ ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by sorry
