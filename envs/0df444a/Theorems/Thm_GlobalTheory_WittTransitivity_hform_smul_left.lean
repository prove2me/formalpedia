-- Prove2me | Theorems.Thm_GlobalTheory_WittTransitivity_hform_smul_left
-- name    : GlobalTheory.WittTransitivity.hform_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:03.740014+00:00
-- url     : https://prove2.me/theorems/87da84e8-aa8c-4214-b364-3326dd370152
-- title:
--   Witt Transitivity: hform smul left
-- statement:
--   The Witt Transitivity construction uses the hform smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L19-L22

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

theorem GlobalTheory.WittTransitivity.hform_smul_left (a : A) (x z : Fin M → A) :
    hform c J (a • x) z = c a * hform c J x z := by sorry
