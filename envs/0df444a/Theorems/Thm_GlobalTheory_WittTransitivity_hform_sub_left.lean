-- Prove2me | Theorems.Thm_GlobalTheory_WittTransitivity_hform_sub_left
-- name    : GlobalTheory.WittTransitivity.hform_sub_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:46.568866+00:00
-- url     : https://prove2.me/theorems/c526ba4c-d6fd-4012-9048-2cd047476932
-- title:
--   Witt Transitivity: hform sub left
-- statement:
--   The Witt Transitivity construction uses the hform sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L11-L13

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

theorem GlobalTheory.WittTransitivity.hform_sub_left (x y z : Fin M → A) :
    hform c J (x - y) z = hform c J x z - hform c J y z := by sorry
