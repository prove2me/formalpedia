-- Prove2me | Theorems.Thm_GlobalTheory_EigFlat_eig_map
-- name    : GlobalTheory.EigFlat.eig_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:53:16.958816+00:00
-- url     : https://prove2.me/theorems/53960416-332f-4033-8951-cd06378583f6
-- title:
--   Eig Flat: eig map
-- statement:
--   The Eig Flat construction uses the eig map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L110-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L110-L121

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

theorem GlobalTheory.EigFlat.eig_map {g m : ℕ} (u : Fin m → Fin g → A) (M : Matrix (Fin g) (Fin g) A) (ρ : A)
    (hu : ∀ k, u k ᵥ* M = ρ • u k) (B : Type) [CommRing B]
    [Algebra A B] (cf : Fin m → B) :
    (cf ᵥ* (Matrix.of u).map (algebraMap A B)) ᵥ* M.map (algebraMap A B)
      = algebraMap A B ρ • (cf ᵥ* (Matrix.of u).map (algebraMap A B)) := by sorry
