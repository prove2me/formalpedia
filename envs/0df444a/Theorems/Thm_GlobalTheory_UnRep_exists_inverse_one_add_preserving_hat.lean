-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_exists_inverse_one_add_preserving_hat
-- name    : GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:38.607538+00:00
-- url     : https://prove2.me/theorems/fcdf903e-96d9-4902-a8e7-7119863c6542
-- title:
--   Un Rep: exists inverse one add preserving hat
-- statement:
--   The Un Rep construction uses the exists inverse one add preserving hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletion.lean#L111-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseOneAddPreservingAdelicCompletion.lean#L111-L311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletion
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
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain

theorem GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F),
    (∀ v, e v ∈ v.adicCompletionIntegers F) →
    (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0) →
    ∀ X : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E),
    (∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      X *ᵥ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) →
    ∃ W : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E),
      (1 + (e ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • (N • X)) * W = 1 ∧
      ∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        W *ᵥ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by sorry
