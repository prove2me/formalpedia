-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtLeastLocus_subset_of_le_ideal
-- name    : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_subset_of_le_ideal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:04.385623+00:00
-- url     : https://prove2.me/theorems/9280740f-0522-5cfc-a4bc-59f1e369ae2b
-- title:
--   Embedded Resolution: order At Least Locus subset of le ideal
-- statement:
--   The Embedded Resolution construction uses the order At Least Locus subset of le ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L581-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L581-L585

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

theorem FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_subset_of_le_ideal {I J : X.IdealSheafData} (h : I ≤ J) (m : ℕ) :
    orderAtLeastLocus J m ⊆ orderAtLeastLocus I m := by sorry
