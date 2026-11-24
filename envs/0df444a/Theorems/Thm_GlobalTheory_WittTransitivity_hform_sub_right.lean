-- Prove2me | Theorems.Thm_GlobalTheory_WittTransitivity_hform_sub_right
-- name    : GlobalTheory.WittTransitivity.hform_sub_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:40.818993+00:00
-- url     : https://prove2.me/theorems/d0348bfb-bc3b-4645-80f9-0999ea385351
-- title:
--   Witt Transitivity: hform sub right
-- statement:
--   The Witt Transitivity construction uses the hform sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L15-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Formalism.UG
open GlobalTheory GlobalTheory.WittTransitivity
variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)

theorem GlobalTheory.WittTransitivity.hform_sub_right (x y z : Fin M → A) :
    hform c J x (y - z) = hform c J x y - hform c J x z := by sorry
