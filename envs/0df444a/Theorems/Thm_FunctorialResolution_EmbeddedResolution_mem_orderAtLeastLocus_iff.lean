-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff
-- name    : FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:48.656114+00:00
-- url     : https://prove2.me/theorems/d9191be0-c13b-4d41-93b8-645790c71cc2
-- title:
--   Embedded Resolution: mem order At Least Locus iff
-- statement:
--   The Embedded Resolution construction uses the mem order At Least Locus iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L546-L547
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L546-L547

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

theorem FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff (I : X.IdealSheafData) (m : ℕ) (x : X) :
    x ∈ orderAtLeastLocus I m ↔ (m : ℕ∞) ≤ orderAt I x := by sorry
