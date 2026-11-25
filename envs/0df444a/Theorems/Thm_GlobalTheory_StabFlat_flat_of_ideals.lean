-- Prove2me | Theorems.Thm_GlobalTheory_StabFlat_flat_of_ideals
-- name    : GlobalTheory.StabFlat.flat_of_ideals
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:16.086601+00:00
-- url     : https://prove2.me/theorems/c21d8904-5fe6-55c9-bc20-8e06b203921b
-- title:
--   Stab Flat: flat of ideals
-- statement:
--   The Stab Flat construction uses the flat of ideals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocalizationOfIsStandardSmooth.lean#L22-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocalizationOfIsStandardSmooth.lean#L22-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth
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

theorem GlobalTheory.StabFlat.flat_of_ideals : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → ¬ IsUnit (σ ϖ) → ∃ I : Ideal (X.presheaf.stalk (j h)), IsSMulRegular (X.presheaf.stalk (j h) ⧸ I) (σ ϖ) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by sorry
