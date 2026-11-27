-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_of_etale_of_surjective
-- name    : GlobalTheory.existsUnique_lift_of_etale_of_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:28.446188+00:00
-- url     : https://prove2.me/theorems/9c0f8062-99de-41d8-a29c-ee38a1044186
-- title:
--   Global Theory: exists Unique lift of etale of surjective
-- statement:
--   The Global Theory construction uses the exists Unique lift of etale of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L246-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L246-L252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory

theorem GlobalTheory.existsUnique_lift_of_etale_of_surjective {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {R R₀ : CommRingCat.{u}} (π : R ⟶ R₀) (hπ : Function.Surjective π)
    (hπ' : IsNilpotent (RingHom.ker π.hom))
    (g : Spec R₀ ⟶ X) (h : Spec R ⟶ S) (w : g ≫ f = Spec.map π ≫ h) :
    ∃! l : Spec R ⟶ X, Spec.map π ≫ l = g ∧ l ≫ f = h := by sorry
