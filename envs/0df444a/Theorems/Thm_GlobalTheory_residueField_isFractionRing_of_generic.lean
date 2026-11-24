-- Prove2me | Theorems.Thm_GlobalTheory_residueField_isFractionRing_of_generic
-- name    : GlobalTheory.residueField_isFractionRing_of_generic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:19.493157+00:00
-- url     : https://prove2.me/theorems/7bbf62e9-0b45-4125-b1f1-ea060d34dfae
-- title:
--   Global Theory: residue Field is Fraction Ring of generic
-- statement:
--   The Global Theory construction uses the residue Field is Fraction Ring of generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsFractionRingStalkGeneric.lean#L6-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsFractionRingStalkGeneric.lean#L6-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsFractionRingStalkGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory

theorem GlobalTheory.residueField_isFractionRing_of_generic : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x),
    IsDomain (X.presheaf.stalk x) → (∀ y, y ⤳ ξ → y = ξ) →
    @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _
      (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) := by sorry
