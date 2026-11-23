-- Prove2me | Theorems.Thm_GlobalTheory_WittTransitivity_conj_hform
-- name    : GlobalTheory.WittTransitivity.conj_hform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:10.692533+00:00
-- url     : https://prove2.me/theorems/993d0978-5026-44f6-872c-6dc7c7154c5c
-- title:
--   Witt Transitivity: conj hform
-- statement:
--   The Witt Transitivity construction uses the conj hform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L29-L33

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

theorem GlobalTheory.WittTransitivity.conj_hform (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j) (x y : Fin M → A) :
    c (hform c J x y) = hform c J y x := by sorry
