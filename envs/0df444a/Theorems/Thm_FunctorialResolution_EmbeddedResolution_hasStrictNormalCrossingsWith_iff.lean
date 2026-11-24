-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_hasStrictNormalCrossingsWith_iff
-- name    : FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:34.493853+00:00
-- url     : https://prove2.me/theorems/9a6031f8-381c-4cdf-9a9c-e14c64833bf3
-- title:
--   Embedded Resolution: has Strict Normal Crossings With iff
-- statement:
--   The Embedded Resolution construction uses the has Strict Normal Crossings With iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L163-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L163-L175

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

theorem FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    HasStrictNormalCrossingsWith p Z E ↔
      ∀ x ∈ Z.support,
        ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
          (S : Finset (Fin m)),
          (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
          (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
          (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
            restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
          restrictIdeal Z U = c.coordIdeal S := by sorry
