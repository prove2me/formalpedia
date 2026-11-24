-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SmallMat_exists_approx
-- name    : GlobalTheory.UnRep.SmallMat.exists_approx
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:21:34.534877+00:00
-- url     : https://prove2.me/theorems/d5008f88-e179-4359-b2da-41caf77619a0
-- title:
--   Small Mat: exists approx
-- statement:
--   The Small Mat construction uses the exists approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatrices.lean#L98-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatrices.lean#L98-L141

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

theorem GlobalTheory.UnRep.SmallMat.exists_approx (S : Set (Fin n → E))
    (hS : ∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ) (hD : 0 < D) :
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w := by sorry
