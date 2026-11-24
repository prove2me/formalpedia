-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdealSheafIterate
-- name    : FunctorialResolution.EmbeddedResolution.le_derivIdealSheafIterate
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:30.566927+00:00
-- url     : https://prove2.me/theorems/d3a1d50e-b69a-4e9a-b63c-98929563303f
-- title:
--   Embedded Resolution: le deriv Ideal Sheaf Iterate
-- statement:
--   The Embedded Resolution construction uses the le deriv Ideal Sheaf Iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L242-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L242-L249

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

theorem FunctorialResolution.EmbeddedResolution.le_derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ) (I : X.IdealSheafData) :
    I ≤ derivIdealSheafIterate k p r I := by sorry
