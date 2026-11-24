-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_orderAt_iff_mem_support
-- name    : FunctorialResolution.EmbeddedResolution.one_le_orderAt_iff_mem_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:07.518497+00:00
-- url     : https://prove2.me/theorems/f5efd074-17a8-4352-998d-5db4f497bb24
-- title:
--   Embedded Resolution: one le order At iff mem support
-- statement:
--   The Embedded Resolution construction uses the one le order At iff mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L218-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L218-L220

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

theorem FunctorialResolution.EmbeddedResolution.one_le_orderAt_iff_mem_support (I : X.IdealSheafData) (x : X) :
    1 ≤ orderAt I x ↔ x ∈ I.support := by sorry
