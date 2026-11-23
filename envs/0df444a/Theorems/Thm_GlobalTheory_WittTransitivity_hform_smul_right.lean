-- Prove2me | Theorems.Thm_GlobalTheory_WittTransitivity_hform_smul_right
-- name    : GlobalTheory.WittTransitivity.hform_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:37.754741+00:00
-- url     : https://prove2.me/theorems/c4127a59-6c9b-4edf-b546-0d523c799c15
-- title:
--   Witt Transitivity: hform smul right
-- statement:
--   The Witt Transitivity construction uses the hform smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L24-L27

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

theorem GlobalTheory.WittTransitivity.hform_smul_right (a : A) (x z : Fin M → A) :
    hform c J x (a • z) = a * hform c J x z := by sorry
