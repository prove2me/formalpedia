-- Prove2me | Theorems.Thm_GlobalTheory_EigFlat_sum_eq
-- name    : GlobalTheory.EigFlat.sum_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:53:10.13821+00:00
-- url     : https://prove2.me/theorems/e932e8fc-83da-432f-856d-c4b2607fcc8d
-- title:
--   Eig Flat: sum eq
-- statement:
--   The Eig Flat construction uses the sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L103-L108

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

theorem GlobalTheory.EigFlat.sum_eq {g m : ℕ} (u : Fin m → Fin g → A) (B : Type) [CommRing B]
    [Algebra A B] (cf : Fin m → B) :
    (∑ k, cf k • (fun j => algebraMap A B (u k j)))
      = cf ᵥ* (Matrix.of u).map (algebraMap A B) := by sorry
