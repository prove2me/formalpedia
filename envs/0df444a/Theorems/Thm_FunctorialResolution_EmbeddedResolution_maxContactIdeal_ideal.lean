-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_maxContactIdeal_ideal
-- name    : FunctorialResolution.EmbeddedResolution.maxContactIdeal_ideal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:53:53.078265+00:00
-- url     : https://prove2.me/theorems/1a92842a-0b8b-593f-94e2-74249ac263e4
-- title:
--   Embedded Resolution: max Contact Ideal ideal
-- statement:
--   The Embedded Resolution construction uses the max Contact Ideal ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L44-L47

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

theorem FunctorialResolution.EmbeddedResolution.maxContactIdeal_ideal (I : X.IdealSheafData) (m : ℕ) (U : X.affineOpens) :
    (maxContactIdeal k p I m).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (m - 1) (I.ideal U) := by sorry
