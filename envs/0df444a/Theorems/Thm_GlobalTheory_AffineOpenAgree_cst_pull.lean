-- Prove2me | Theorems.Thm_GlobalTheory_AffineOpenAgree_cst_pull
-- name    : GlobalTheory.AffineOpenAgree.cst_pull
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:55:13.754899+00:00
-- url     : https://prove2.me/theorems/cab153dc-bd67-4e9b-b81d-f4929feda4bb
-- title:
--   Affine Open Agree: cst pull
-- statement:
--   The Affine Open Agree construction uses the cst pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfAgreeOnAffineOpenGenerators.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfAgreeOnAffineOpenGenerators.lean#L21-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfAgreeOnAffineOpenGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.AffineOpenAgree

theorem GlobalTheory.AffineOpenAgree.cst_pull {R : Type} [CommRing R] {X W : Scheme.{0}} (sm : X ⟶ Spec (CommRingCat.of R)) (N : X.Opens)
    (c : W ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ N) (x : R) :
    (W.presheaf.map (homOfLE hc).op).hom ((c.app N).hom (GlobalTheory.AbLaw.cst sm N x)) =
      (c ≫ sm).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := by sorry
