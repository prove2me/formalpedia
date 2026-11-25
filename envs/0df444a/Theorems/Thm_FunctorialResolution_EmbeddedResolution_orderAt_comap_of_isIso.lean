-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_comap_of_isIso
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isIso
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:36.27556+00:00
-- url     : https://prove2.me/theorems/313c6f06-9901-5617-8c11-67e629eba209
-- title:
--   Embedded Resolution: order At comap of is Iso
-- statement:
--   The Embedded Resolution construction uses the order At comap of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L539-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L539-L541

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
open CategoryTheory

theorem FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f] (J : B.IdealSheafData)
    (x : ↥A) : orderAt (J.comap f) x = orderAt J (f.base x) := by sorry
