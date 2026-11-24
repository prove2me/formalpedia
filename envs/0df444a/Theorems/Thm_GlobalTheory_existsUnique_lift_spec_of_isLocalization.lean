-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_spec_of_isLocalization
-- name    : GlobalTheory.existsUnique_lift_spec_of_isLocalization
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:30.975197+00:00
-- url     : https://prove2.me/theorems/145013b2-2da8-49d2-b30c-012377b63bf3
-- title:
--   Global Theory: exists Unique lift spec of is Localization
-- statement:
--   The Global Theory construction uses the exists Unique lift spec of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L259-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L259-L266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {Z Y : Scheme.{u}}

theorem GlobalTheory.existsUnique_lift_spec_of_isLocalization [IsIntegrallyClosed R] (M : Submonoid R)
    (hM : M ≤ nonZeroDivisors R) [IsLocalization M R']
    (p : Z ⟶ Y) [IsIntegralHom p] (a : Spec (.of R') ⟶ Z) (b : Spec (.of R) ⟶ Y)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ b) :
    ∃! c : Spec (.of R) ⟶ Z,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ c = a ∧ c ≫ p = b := by sorry
