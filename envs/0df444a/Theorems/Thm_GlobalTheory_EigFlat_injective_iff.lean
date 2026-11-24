-- Prove2me | Theorems.Thm_GlobalTheory_EigFlat_injective_iff
-- name    : GlobalTheory.EigFlat.injective_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:53:07.442793+00:00
-- url     : https://prove2.me/theorems/24603539-f03b-464e-a88d-40fd8c685b62
-- title:
--   Eig Flat: injective iff
-- statement:
--   The Eig Flat construction uses the injective iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L50-L58

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

theorem GlobalTheory.EigFlat.injective_iff {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (U : Matrix a b A) (B : Type) [CommRing B] [Algebra A B] :
    Function.Injective (LinearMap.lTensor B U.vecMulLinear) ↔
      Function.Injective (fun cf : a → B => cf ᵥ* U.map (algebraMap A B)) := by sorry
