-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtLeastLocus_subset_orderAtLeastLocus_pow
-- name    : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_subset_orderAtLeastLocus_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:51.458495+00:00
-- url     : https://prove2.me/theorems/a5615ee9-61a2-4952-8d62-d7bcf034c0ad
-- title:
--   Embedded Resolution: order At Least Locus subset order At Least Locus pow
-- statement:
--   The Embedded Resolution construction uses the order At Least Locus subset order At Least Locus pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L595-L601
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L595-L601

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

theorem FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_subset_orderAtLeastLocus_pow (I : X.IdealSheafData) (c m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (I ^ c) (c * m) := by sorry
