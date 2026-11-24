-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:03.629107+00:00
-- url     : https://prove2.me/theorems/5fd06e62-1971-4e1f-b141-15b6d2efb846
-- title:
--   Embedded Resolution: deriv Ideal Sheaf Iterate ideal
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Sheaf Iterate ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L229-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L229-L240

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

theorem FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ)
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheafIterate k p r I).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) r (I.ideal U) := by sorry
