-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_maxContactIdeal_eq_derivIdealSheafIterate
-- name    : FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:16:02.022554+00:00
-- url     : https://prove2.me/theorems/ca55b9bc-efa1-43ab-be13-50f0bcfedd1b
-- title:
--   Embedded Resolution: max Contact Ideal eq deriv Ideal Sheaf Iterate
-- statement:
--   The Embedded Resolution construction uses the max Contact Ideal eq deriv Ideal Sheaf Iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L37-L39

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

theorem FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate (I : X.IdealSheafData) (m : ℕ) :
    maxContactIdeal k p I m = derivIdealSheafIterate k p (m - 1) I := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate
