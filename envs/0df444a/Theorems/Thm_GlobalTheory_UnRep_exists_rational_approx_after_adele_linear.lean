-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_exists_rational_approx_after_adele_linear
-- name    : GlobalTheory.UnRep.exists_rational_approx_after_adele_linear
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:45.596315+00:00
-- url     : https://prove2.me/theorems/0b8c045f-df4c-4ac4-abac-80731535d890
-- title:
--   Un Rep: exists rational approx after adele linear
-- statement:
--   The Un Rep construction uses the exists rational approx after adele linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalMatrixApproxAdeleLinearMap.lean#L11-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalMatrixApproxAdeleLinearMap.lean#L11-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMap
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
open GlobalTheory.UnRep.SmallMat

theorem GlobalTheory.UnRep.exists_rational_approx_after_adele_linear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (φ : Matrix (Fin n) (Fin n) (RA F E) →+ Matrix (Fin n) (Fin n) (RA F E)), (∀ (a : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), φ ((a ⊗ₜ[F] (1 : E) : RA F E) • M) = (a ⊗ₜ[F] (1 : E) : RA F E) • φ M) → ∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), φ (M - fm F M₀) *ᵥ z = D • w := by sorry
