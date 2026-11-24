-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SmallMat_exists_coprime_small
-- name    : GlobalTheory.UnRep.SmallMat.exists_coprime_small
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:23:29.938811+00:00
-- url     : https://prove2.me/theorems/a137b732-4291-4572-8d1f-8b38646fee75
-- title:
--   Small Mat: exists coprime small
-- statement:
--   The Small Mat construction uses the exists coprime small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatrices.lean#L143-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatrices.lean#L143-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
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
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SmallMat
open GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.UnRep.SmallMat.exists_coprime_small (S : Set (Fin n → E)) (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (hD : 0 < D)
    (hM : ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (he : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F S, ∃ w ∈ hat F S,
      t • (((e ⊗ₜ[F] (1 : E) : RA F E) • M) *ᵥ z) = D • w := by sorry
