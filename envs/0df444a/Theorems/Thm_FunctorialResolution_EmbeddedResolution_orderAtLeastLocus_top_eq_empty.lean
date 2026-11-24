-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtLeastLocus_top_eq_empty
-- name    : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_top_eq_empty
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:01.541451+00:00
-- url     : https://prove2.me/theorems/4eff3393-557d-4753-a137-67ad8828ced5
-- title:
--   Embedded Resolution: order At Least Locus top eq empty
-- statement:
--   The Embedded Resolution construction uses the order At Least Locus top eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L567-L572
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L567-L572

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

theorem FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_top_eq_empty (m : ℕ) (hm : 1 ≤ m) :
    orderAtLeastLocus (⊤ : X.IdealSheafData) m = ∅ := by sorry
