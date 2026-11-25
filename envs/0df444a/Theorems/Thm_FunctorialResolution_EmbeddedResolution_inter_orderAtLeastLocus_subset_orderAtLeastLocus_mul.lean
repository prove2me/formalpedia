-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul
-- name    : FunctorialResolution.EmbeddedResolution.inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:38.872452+00:00
-- url     : https://prove2.me/theorems/b5833e33-ff9c-5fe5-b641-ea1b69f36caf
-- title:
--   Embedded Resolution: inter order At Least Locus subset order At Least Locus mul
-- statement:
--   The Embedded Resolution construction uses the inter order At Least Locus subset order At Least Locus mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L587-L593
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L587-L593

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

theorem FunctorialResolution.EmbeddedResolution.inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul (I J : X.IdealSheafData) (m m' : ℕ) :
    orderAtLeastLocus I m ∩ orderAtLeastLocus J m' ⊆ orderAtLeastLocus (I * J) (m + m') := by sorry
