-- Prove2me | Theorems.Thm_GlobalTheory_StabFlat_eq_ker_stalkMap_of_points
-- name    : GlobalTheory.StabFlat.eq_ker_stalkMap_of_points
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:22:59.641265+00:00
-- url     : https://prove2.me/theorems/e5382573-cd67-4ac6-838a-d7c6329adc10
-- title:
--   Stab Flat: eq ker stalk Map of points
-- statement:
--   The Stab Flat construction uses the eq ker stalk Map of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatClosedSubschemeFiniteOverLocalRing.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatClosedSubschemeFiniteOverLocalRing.lean#L8-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatClosedSubschemeFiniteOverLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat

theorem GlobalTheory.StabFlat.eq_ker_stalkMap_of_points {X H : Scheme.{0}} (j : H ⟶ X) [IsClosedImmersion j] (h : H)
    (I : Ideal (X.presheaf.stalk (j h)))
    (hI : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔
        I ≤ RingHom.ker φ) : I = RingHom.ker (j.stalkMap h).hom := by sorry
