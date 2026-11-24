-- Prove2me | Theorems.Thm_GlobalTheory_Retract_of_hasRingHomProperty
-- name    : GlobalTheory.Retract.of_hasRingHomProperty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:52.487119+00:00
-- url     : https://prove2.me/theorems/efd4a066-a958-43b4-8938-a52079759392
-- title:
--   Retract: of has Ring Hom Property
-- statement:
--   The Retract construction uses the of has Ring Hom Property property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L173-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L173-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}

theorem GlobalTheory.Retract.of_hasRingHomProperty (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R A : Type u} [CommRing R] [CommRing A], (R →+* A) → Prop} [HasRingHomProperty P Q]
    (hQ : ∀ {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (s : A →ₐ[R] B) (p : B →ₐ[R] A), p.comp s = AlgHom.id R A →
        Q (algebraMap R B) → Q (algebraMap R A))
    (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) (hg : P g) : P f := by sorry
