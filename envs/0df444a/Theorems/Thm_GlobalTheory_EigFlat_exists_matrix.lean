-- Prove2me | Theorems.Thm_GlobalTheory_EigFlat_exists_matrix
-- name    : GlobalTheory.EigFlat.exists_matrix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:53:06.284802+00:00
-- url     : https://prove2.me/theorems/c36e7d84-118c-41f9-a4d4-b36662bb4aa2
-- title:
--   Eig Flat: exists matrix
-- statement:
--   The Eig Flat construction uses the exists matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L60-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L60-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open GlobalTheory.EigFlat
variable {A : Type} [CommRing A]

theorem GlobalTheory.EigFlat.exists_matrix [IsNoetherianRing A] {I : Type} {g : ℕ} (D : I → Matrix (Fin g) (Fin g) A) :
    ∃ (n : ℕ) (H : Matrix (Fin g) (Fin n × Fin g) A), ∀ (B : Type) [CommRing B] [Algebra A B]
      (w : Fin g → B), w ᵥ* H.map (algebraMap A B) = 0 ↔
        ∀ i, w ᵥ* (D i).map (algebraMap A B) = 0 := by sorry
