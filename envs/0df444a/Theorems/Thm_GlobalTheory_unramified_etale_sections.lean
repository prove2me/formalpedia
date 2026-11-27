-- Prove2me | Theorems.Thm_GlobalTheory_unramified_etale_sections
-- name    : GlobalTheory.unramified_etale_sections
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:12.40127+00:00
-- url     : https://prove2.me/theorems/9250ed81-5b1e-4bf0-a6af-d83236714d02
-- title:
--   Global Theory: unramified etale sections
-- statement:
--   The Global Theory construction uses the unramified etale sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L367-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L367-L387

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

theorem GlobalTheory.unramified_etale_sections :
    (∀ {X S T : Scheme.{u}} (f : X ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f]
      [IsSeparated f] (a b : T ⟶ X), a ≫ f = b ≫ f →
        IsOpenImmersion (equalizer.ι a b) ∧ IsClosedImmersion (equalizer.ι a b)) ∧
    (∀ {X S T : Scheme.{u}} (f : X ⟶ S) [FormallyUnramified f] [LocallyOfFiniteType f]
      [IsSeparated f] [ConnectedSpace T] (a b : T ⟶ X), a ≫ f = b ≫ f →
        ∀ (k : Type u) [Field k] (j : Spec (.of k) ⟶ T), j ≫ a = j ≫ b → a = b) ∧
    (∀ {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] [IsSeparated f] (s : S ⟶ X), s ≫ f = 𝟙 S →
        IsOpenImmersion s ∧ IsClosedImmersion s) ∧
    (∀ {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f] (i : T₀ ⟶ T) [IsClosedImmersion i],
      IsNilpotent i.ker → ∀ (g : T₀ ⟶ X) (h : T ⟶ S), g ≫ f = i ≫ h →
        ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h) ∧
    (∀ (R : Type u) [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
      [Etale f], Function.Bijective (restrictPoints f (𝟙 _)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) := by sorry
