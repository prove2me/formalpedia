-- Prove2me | Theorems.Thm_GlobalTheory_WittTransitivity_exists_mem_UJ
-- name    : GlobalTheory.WittTransitivity.exists_mem_UJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:10.585495+00:00
-- url     : https://prove2.me/theorems/452b0cf8-0087-475c-8d31-4d774c3e6c3b
-- title:
--   Witt Transitivity: exists mem UJ
-- statement:
--   The Witt Transitivity construction uses the exists mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L44-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsReflection.lean#L44-L72

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

theorem GlobalTheory.WittTransitivity.exists_mem_UJ (hdet : IsUnit J.det) (g : Matrix (Fin M) (Fin M) A)
    (hg : ∀ y z, hform c J (g *ᵥ y) (g *ᵥ z) = hform c J y z) :
    ∃ G ∈ UJ c J, (G : Matrix (Fin M) (Fin M) A) = g := by sorry
