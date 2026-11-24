-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_hasStrictNormalCrossingsWith_of_forall_exists_etaleChart
-- name    : FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_of_forall_exists_etaleChart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:36.527804+00:00
-- url     : https://prove2.me/theorems/db22b6dd-b3ec-46f3-a83a-c6584e51b598
-- title:
--   Embedded Resolution: has Strict Normal Crossings With of forall exists etale Chart
-- statement:
--   The Embedded Resolution construction uses the has Strict Normal Crossings With of forall exists etale Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L189-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L189-L201

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

theorem FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_of_forall_exists_etaleChart {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData}
    {E : List X.IdealSheafData}
    (h : ∀ x ∈ Z.support,
      ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
        (S : Finset (Fin m)),
        (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
        (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
        (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
          restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
        restrictIdeal Z U = c.coordIdeal S) :
    HasStrictNormalCrossingsWith p Z E := by sorry
