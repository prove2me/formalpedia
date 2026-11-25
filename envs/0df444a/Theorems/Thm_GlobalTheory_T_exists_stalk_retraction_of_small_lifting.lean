-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_stalk_retraction_of_small_lifting
-- name    : GlobalTheory.T.exists_stalk_retraction_of_small_lifting
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:17.047003+00:00
-- url     : https://prove2.me/theorems/f4d79b66-5dd6-4534-96c0-5d45872e69ff
-- title:
--   T: exists stalk retraction of small lifting
-- statement:
--   The T construction uses the exists stalk retraction of small lifting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLiftingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLiftingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLiftingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_stalk_retraction_of_small_lifting : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → ∀ (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))], Function.Surjective (f.residueFieldMap x).hom → ∀ n : ℕ, ∃ ψ : X.presheaf.stalk x →+* Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1), ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ := by sorry
