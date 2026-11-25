-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_one
-- name    : FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:53:47.577352+00:00
-- url     : https://prove2.me/theorems/fc7a9c5d-0a2e-5ec5-b4b4-480b37d83234
-- title:
--   Embedded Resolution: log Deriv Ideal Sheaf Iterate one
-- statement:
--   The Embedded Resolution construction uses the log Deriv Ideal Sheaf Iterate one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean#L81-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean#L81-L85

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
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

theorem FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_one (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P 1 I = logDerivIdealSheaf k p P I := by sorry
