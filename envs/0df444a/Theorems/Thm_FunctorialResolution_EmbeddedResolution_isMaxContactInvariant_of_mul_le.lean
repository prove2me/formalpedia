-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isMaxContactInvariant_of_mul_le
-- name    : FunctorialResolution.EmbeddedResolution.isMaxContactInvariant_of_mul_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:13.29867+00:00
-- url     : https://prove2.me/theorems/6c361fa3-d265-4fa3-b5f3-7634b64b7d19
-- title:
--   Embedded Resolution: is Max Contact Invariant of mul le
-- statement:
--   The Embedded Resolution construction uses the is Max Contact Invariant of mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L52-L54

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

theorem FunctorialResolution.EmbeddedResolution.isMaxContactInvariant_of_mul_le {I : X.IdealSheafData} {m : ℕ}
    (h : maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I) : IsMaxContactInvariant k p I m := by sorry
