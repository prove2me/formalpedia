-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_inverse_one_add_preserving_adelicCompletion
-- name    : GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:21.1402+00:00
-- url     : https://prove2.me/theorems/eb626960-4663-4d1f-b989-6f50a433879b
-- title:
--   T: exists inverse one add preserving adelic Completion
-- statement:
--   The T construction uses the exists inverse one add preserving adelic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
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

theorem GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F), (∀ v, e v ∈ v.adicCompletionIntegers F) → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0) → ∀ X : Matrix (Fin n) (Fin n) (RA F E), (∀ z ∈ hat F (L : Set (Fin n → E)), X *ᵥ z ∈ hat F (L : Set (Fin n → E))) → ∃ W : Matrix (Fin n) (Fin n) (RA F E), (1 + (e ⊗ₜ[F] (1 : E) : RA F E) • (N • X)) * W = 1 ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), W *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by sorry
