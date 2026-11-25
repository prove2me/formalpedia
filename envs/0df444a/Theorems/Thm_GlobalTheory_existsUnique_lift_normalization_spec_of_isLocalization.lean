-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_normalization_spec_of_isLocalization
-- name    : GlobalTheory.existsUnique_lift_normalization_spec_of_isLocalization
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:45:16.964817+00:00
-- url     : https://prove2.me/theorems/136ad261-3d10-5ae6-b73a-3a20b3ea61b8
-- title:
--   Global Theory: exists Unique lift normalization spec of is Localization
-- statement:
--   The Global Theory construction uses the exists Unique lift normalization spec of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L276-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueLiftSpecOfIsLocalizationAway.lean#L276-L284

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

theorem GlobalTheory.existsUnique_lift_normalization_spec_of_isLocalization [IsIntegrallyClosed R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) [IsLocalization M R']
    (χ₀ : Spec (.of R) ⟶ Y) (χ₁ : Spec (.of R') ⟶ X)
    (h : χ₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ χ₀) :
    ∃! χ : Spec (.of R) ⟶ f.normalization,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ χ = χ₁ ≫ f.toNormalization ∧
        χ ≫ f.fromNormalization = χ₀ := by sorry
