-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:59:32.246243+00:00
-- url     : https://prove2.me/theorems/65b174e8-29cf-4fd3-8968-899134a1af8e
-- title:
--   Embedded Resolution: deriv Ideal Sheaf ideal
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Sheaf ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L131-L135

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

theorem FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheaf k p I).ideal U = @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
