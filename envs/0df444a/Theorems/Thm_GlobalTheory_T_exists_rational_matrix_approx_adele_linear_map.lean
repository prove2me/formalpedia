-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_rational_matrix_approx_adele_linear_map
-- name    : GlobalTheory.T.exists_rational_matrix_approx_adele_linear_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:40:00.031121+00:00
-- url     : https://prove2.me/theorems/7207083a-9598-4408-8f0a-3334c8b30a7b
-- title:
--   T: exists rational matrix approx adele linear map
-- statement:
--   The T construction uses the exists rational matrix approx adele linear map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalMatrixApproxAdeleLinearMapStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalMatrixApproxAdeleLinearMapStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_rational_matrix_approx_adele_linear_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (φ : Matrix (Fin n) (Fin n) (RA F E) →+ Matrix (Fin n) (Fin n) (RA F E)), (∀ (a : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), φ ((a ⊗ₜ[F] (1 : E) : RA F E) • M) = (a ⊗ₜ[F] (1 : E) : RA F E) • φ M) → ∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), φ (M - fm F M₀) *ᵥ z = D • w := by sorry
