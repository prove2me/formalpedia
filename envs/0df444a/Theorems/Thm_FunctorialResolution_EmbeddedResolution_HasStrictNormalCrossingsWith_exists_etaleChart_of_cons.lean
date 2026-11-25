-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart_of_cons
-- name    : FunctorialResolution.EmbeddedResolution.HasStrictNormalCrossingsWith.exists_etaleChart_of_cons
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:47.441645+00:00
-- url     : https://prove2.me/theorems/52fa9705-85af-4527-939d-73088a81d593
-- title:
--   Has Strict Normal Crossings With: exists etale Chart of cons
-- statement:
--   The Has Strict Normal Crossings With construction uses the exists etale Chart of cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L223-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L223-L267

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.HasStrictNormalCrossingsWith.exists_etaleChart_of_cons {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData}
    {H : X.IdealSheafData} {E : List X.IdealSheafData}
    (h : HasStrictNormalCrossingsWith p Z (H :: E)) {x : X} (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (S : Finset (Fin m))
      (aH : Option (Fin m)) (a : ℕ → Option (Fin m)),
      restrictIdeal Z U = c.coordIdeal S ∧
      (aH = none → restrictIdeal H U = ⊤) ∧
      (∀ t : Fin m, aH = some t → restrictIdeal H U = c.coordIdeal {t}) ∧
      (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      (∀ i < E.length, ∀ t : Fin m, a i = some t → aH ≠ some t) ∧
      (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) := by sorry
