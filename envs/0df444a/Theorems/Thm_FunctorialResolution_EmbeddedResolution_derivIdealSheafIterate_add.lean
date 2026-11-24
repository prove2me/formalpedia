-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_add
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_add
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:40.57489+00:00
-- url     : https://prove2.me/theorems/1e0b27f1-c809-4c9a-b7c0-d7bdae91fc91
-- title:
--   Embedded Resolution: deriv Ideal Sheaf Iterate add
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Sheaf Iterate add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L220-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L220-L227

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
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

theorem FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_add (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r s : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k p (r + s) I =
      derivIdealSheafIterate k p r (derivIdealSheafIterate k p s I) := by sorry
