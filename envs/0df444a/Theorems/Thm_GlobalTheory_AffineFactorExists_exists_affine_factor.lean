-- Prove2me | Theorems.Thm_GlobalTheory_AffineFactorExists_exists_affine_factor
-- name    : GlobalTheory.AffineFactorExists.exists_affine_factor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:54:33.900029+00:00
-- url     : https://prove2.me/theorems/c469970b-41c2-4087-8ea9-3c7c413e1367
-- title:
--   Affine Factor Exists: exists affine factor
-- statement:
--   The Affine Factor Exists construction uses the exists affine factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFactorFractionRing.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFactorFractionRing.lean#L7-L19

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

theorem GlobalTheory.AffineFactorExists.exists_affine_factor {F : Type} [Field F] {X : Scheme.{0}}
    (x : Spec (CommRingCat.of F) ⟶ X) :
    ∃ (A : CommRingCat.{0}) (ι : Spec A ⟶ X) (_ : IsOpenImmersion ι) (φ : A ⟶ CommRingCat.of F),
      Spec.map φ ≫ ι = x := by sorry
