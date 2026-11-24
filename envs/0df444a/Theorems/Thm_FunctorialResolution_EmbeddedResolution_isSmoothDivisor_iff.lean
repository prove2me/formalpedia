-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isSmoothDivisor_iff
-- name    : FunctorialResolution.EmbeddedResolution.isSmoothDivisor_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:08.855923+00:00
-- url     : https://prove2.me/theorems/be4a9bbf-b4ea-41cb-abba-4b9d080adcee
-- title:
--   Embedded Resolution: is Smooth Divisor iff
-- statement:
--   The Embedded Resolution construction uses the is Smooth Divisor iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L90-L94

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

theorem FunctorialResolution.EmbeddedResolution.isSmoothDivisor_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) :
    IsSmoothDivisor p D ↔
      Blowup.IsLocallyGeneratedByNonZeroDivisor D ∧ AlgebraicGeometry.Smooth (D.subschemeι ≫ p) := by sorry
