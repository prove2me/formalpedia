-- Prove2me | Theorems.Thm_GlobalTheory_EigFlat_exact_iff
-- name    : GlobalTheory.EigFlat.exact_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:53:15.428649+00:00
-- url     : https://prove2.me/theorems/66f82ab3-d20b-40ab-b192-9f2d50397f2e
-- title:
--   Eig Flat: exact iff
-- statement:
--   The Eig Flat construction uses the exact iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L23-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L23-L48

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

theorem GlobalTheory.EigFlat.exact_iff {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    [DecidableEq b] [DecidableEq c] (U : Matrix a b A) (H : Matrix b c A)
    (B : Type) [CommRing B] [Algebra A B] :
    Function.Exact (LinearMap.lTensor B U.vecMulLinear) (LinearMap.lTensor B H.vecMulLinear) ↔
      ∀ w : b → B, w ᵥ* H.map (algebraMap A B) = 0 ↔
        ∃ cf : a → B, cf ᵥ* U.map (algebraMap A B) = w := by sorry
