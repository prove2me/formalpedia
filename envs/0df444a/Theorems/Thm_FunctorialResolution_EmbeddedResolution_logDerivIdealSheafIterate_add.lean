-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_add
-- name    : FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:53:55.02702+00:00
-- url     : https://prove2.me/theorems/954129ed-a45b-445f-9199-ecbafa99e066
-- title:
--   Embedded Resolution: log Deriv Ideal Sheaf Iterate add
-- statement:
--   The Embedded Resolution construction uses the log Deriv Ideal Sheaf Iterate add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean#L87-L97

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

theorem FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_add (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (P : X.IdealSheafData) (r s : ℕ) (I : X.IdealSheafData) :
    logDerivIdealSheafIterate k p P (r + s) I =
      logDerivIdealSheafIterate k p P r (logDerivIdealSheafIterate k p P s I) := by sorry
