-- Prove2me | Theorems.Thm_GlobalTheory_SmallLift_step
-- name    : GlobalTheory.SmallLift.step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:26.138945+00:00
-- url     : https://prove2.me/theorems/0e52fed3-0eb7-4a69-837b-19236f575fe1
-- title:
--   Small Lift: step
-- statement:
--   The Small Lift construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLifting.lean#L16-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLifting.lean#L16-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.SmallLift

theorem GlobalTheory.SmallLift.step {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) [IsLocalRing (C ⧸ I)]
    (H : ∀ (a : Spec (CommRingCat.of (C ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of C) ⟶ Y),
      a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
      ∃ l : Spec (CommRingCat.of C) ⟶ X,
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b)
    (π : Y.presheaf.stalk (f x) ⟶ CommRingCat.of C)
    (ψ : X.presheaf.stalk x ⟶ CommRingCat.of (C ⧸ I)) [IsLocalHom ψ.hom]
    (hψ : ψ.hom.comp (f.stalkMap x).hom = (Ideal.Quotient.mk I).comp π.hom) :
    ∃ g : X.presheaf.stalk x →+* C, IsLocalHom g ∧ g.comp (f.stalkMap x).hom = π.hom := by sorry
