-- Prove2me | Theorems.Thm_GlobalTheory_AffineOpenAgree_app_restrict_eq
-- name    : GlobalTheory.AffineOpenAgree.app_restrict_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:55:28.110288+00:00
-- url     : https://prove2.me/theorems/e6cd9936-0633-4f95-8943-0ef38e966e28
-- title:
--   Affine Open Agree: app restrict eq
-- statement:
--   The Affine Open Agree construction uses the app restrict eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfAgreeOnAffineOpenGenerators.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfAgreeOnAffineOpenGenerators.lean#L7-L19

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

theorem GlobalTheory.AffineOpenAgree.app_restrict_eq (X W : Scheme.{0}) (N : X.Opens) (c : W ⟶ N.toScheme) (hc : ⊤ ≤ (c ≫ N.ι) ⁻¹ᵁ N) :
    (c ≫ N.ι).app N ≫ W.presheaf.map (homOfLE hc).op = N.topIso.inv ≫ c.appTop := by sorry
