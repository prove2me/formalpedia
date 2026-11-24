-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_eq_ofIdealTop_span_coord
-- name    : FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_eq_ofIdealTop_span_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:31.377854+00:00
-- url     : https://prove2.me/theorems/bc52097e-ea82-4d35-9f19-f76ea04d9d68
-- title:
--   Embedded Resolution: coord Subspace Ideal eq of Ideal Top span coord
-- statement:
--   The Embedded Resolution construction uses the coord Subspace Ideal eq of Ideal Top span coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L116-L121

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

theorem FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_eq_ofIdealTop_span_coord (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    coordSubspaceIdeal k m S =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span
          ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
            (S : Set (Fin m)))) := by sorry
