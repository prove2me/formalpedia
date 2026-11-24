-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_one_iff
-- name    : FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:24.164345+00:00
-- url     : https://prove2.me/theorems/15e3bc2f-5bb6-4688-b77e-ea85789a2310
-- title:
--   Embedded Resolution: mem order At Least Locus one iff
-- statement:
--   The Embedded Resolution construction uses the mem order At Least Locus one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L559-L561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L559-L561

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

theorem FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_one_iff (I : X.IdealSheafData) (x : X) :
    x ∈ orderAtLeastLocus I 1 ↔ x ∈ I.support := by sorry
