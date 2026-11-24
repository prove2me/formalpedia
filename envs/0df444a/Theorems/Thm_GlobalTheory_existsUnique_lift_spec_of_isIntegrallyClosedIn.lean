-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_spec_of_isIntegrallyClosedIn
-- name    : GlobalTheory.existsUnique_lift_spec_of_isIntegrallyClosedIn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:07.827685+00:00
-- url     : https://prove2.me/theorems/4bc1746a-f3bb-48ee-a21c-72218256bce7
-- title:
--   Global Theory: exists Unique lift spec of is Integrally Closed In
-- statement:
--   The Global Theory construction uses the exists Unique lift spec of is Integrally Closed In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L251-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L251-L257

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

theorem GlobalTheory.existsUnique_lift_spec_of_isIntegrallyClosedIn [IsIntegrallyClosedIn R R']
    (p : Z ⟶ Y) [IsIntegralHom p] (a : Spec (.of R') ⟶ Z) (b : Spec (.of R) ⟶ Y)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ b) :
    ∃! c : Spec (.of R) ⟶ Z,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ c = a ∧ c ≫ p = b := by sorry
