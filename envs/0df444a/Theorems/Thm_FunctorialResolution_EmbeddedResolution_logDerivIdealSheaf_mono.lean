-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheaf_mono
-- name    : FunctorialResolution.EmbeddedResolution.logDerivIdealSheaf_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:33.296109+00:00
-- url     : https://prove2.me/theorems/bda212d2-313c-48e8-9a53-44ca9984d04c
-- title:
--   Embedded Resolution: log Deriv Ideal Sheaf mono
-- statement:
--   The Embedded Resolution construction uses the log Deriv Ideal Sheaf mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealSheaf.lean#L49-L54

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

theorem FunctorialResolution.EmbeddedResolution.logDerivIdealSheaf_mono (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (P : X.IdealSheafData) :
    Monotone (logDerivIdealSheaf k p P) := by sorry
