-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_mono
-- name    : FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_mono
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:53:41.909972+00:00
-- url     : https://prove2.me/theorems/65040dfc-b56b-5ee0-816c-8aa02233cbe1
-- title:
--   Embedded Resolution: log Deriv Ideal Sheaf Iterate mono
-- statement:
--   The Embedded Resolution construction uses the log Deriv Ideal Sheaf Iterate mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean#L112-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean#L112-L124

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

theorem FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_mono (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r : ℕ) :
    Monotone (logDerivIdealSheafIterate k p P r) := by sorry
