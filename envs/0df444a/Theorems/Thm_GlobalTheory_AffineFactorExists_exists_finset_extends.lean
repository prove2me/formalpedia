-- Prove2me | Theorems.Thm_GlobalTheory_AffineFactorExists_exists_finset_extends
-- name    : GlobalTheory.AffineFactorExists.exists_finset_extends
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:54:37.581875+00:00
-- url     : https://prove2.me/theorems/5afd380d-ebe8-4c80-8a76-3e8749aaabd9
-- title:
--   Affine Factor Exists: exists finset extends
-- statement:
--   The Affine Factor Exists construction uses the exists finset extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFactorFractionRing.lean#L50-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFactorFractionRing.lean#L50-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFactorFractionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineFactorExists

theorem GlobalTheory.AffineFactorExists.exists_finset_extends (V F : Type) [CommRing V] [Field F] [Algebra V F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ (0 : F) ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by sorry
