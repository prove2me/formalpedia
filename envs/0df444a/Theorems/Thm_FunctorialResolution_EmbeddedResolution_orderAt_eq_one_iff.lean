-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_one_iff
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_eq_one_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:05.144962+00:00
-- url     : https://prove2.me/theorems/21fcd39b-1103-45f0-b0e3-576b3a41b517
-- title:
--   Embedded Resolution: order At eq one iff
-- statement:
--   The Embedded Resolution construction uses the order At eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L254-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L254-L278

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_eq_one_iff (I : X.IdealSheafData) (x : X) :
    orderAt I x = 1 ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        ¬ stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by sorry
