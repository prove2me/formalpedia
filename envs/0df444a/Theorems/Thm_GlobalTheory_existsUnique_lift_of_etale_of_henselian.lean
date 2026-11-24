-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_lift_of_etale_of_henselian
-- name    : GlobalTheory.existsUnique_lift_of_etale_of_henselian
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:09.593104+00:00
-- url     : https://prove2.me/theorems/63e73157-dc1d-4263-afcd-e6116bfde2a5
-- title:
--   Global Theory: exists Unique lift of etale of henselian
-- statement:
--   The Global Theory construction uses the exists Unique lift of etale of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L292-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L292-L336

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

theorem GlobalTheory.existsUnique_lift_of_etale_of_henselian {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {R K : Type u} [CommRing R] [HenselianLocalRing R] [Field K] (π : R →+* K)
    (hπ : Function.Surjective π) (g : Spec (.of K) ⟶ X) (h : Spec (.of R) ⟶ S)
    (w : g ≫ f = Spec.map (CommRingCat.ofHom π) ≫ h) :
    ∃! l : Spec (.of R) ⟶ X, Spec.map (CommRingCat.ofHom π) ≫ l = g ∧ l ≫ f = h := by sorry
