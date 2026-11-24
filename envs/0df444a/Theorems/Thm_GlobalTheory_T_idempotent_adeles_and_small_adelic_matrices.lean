-- Prove2me | Theorems.Thm_GlobalTheory_T_idempotent_adeles_and_small_adelic_matrices
-- name    : GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:09.464843+00:00
-- url     : https://prove2.me/theorems/1f5a7636-c752-42cc-8d78-ca0f69d26383
-- title:
--   T: idempotent adeles and small adelic matrices
-- statement:
--   The T construction uses the idempotent adeles and small adelic matrices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatricesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatricesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
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

theorem GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0) ∧ (∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))) ∧ (∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), (M - fm F M₀) *ᵥ z = D • w) ∧ (∀ (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), 0 < D → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) → ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), t • (((e ⊗ₜ[F] (1 : E)) • M) *ᵥ z) = D • w) ∧ ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ z ∈ hat F (L : Set (Fin n → E)), (a ⊗ₜ[F] (1 : E)) • z ∈ hat F (L : Set (Fin n → E)) := by sorry
