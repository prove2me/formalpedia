-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_mul_le
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealSheaf_mul_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:21.539047+00:00
-- url     : https://prove2.me/theorems/21dbc65b-f1d4-401b-adb2-d8daea7bed31
-- title:
--   Embedded Resolution: deriv Ideal Sheaf mul le
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Sheaf mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L157-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L157-L182

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

theorem FunctorialResolution.EmbeddedResolution.derivIdealSheaf_mul_le (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I J : X.IdealSheafData) :
    derivIdealSheaf k p (I * J) ≤ I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I := by sorry
