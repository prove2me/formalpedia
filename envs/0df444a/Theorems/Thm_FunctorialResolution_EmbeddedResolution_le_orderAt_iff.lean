-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
-- name    : FunctorialResolution.EmbeddedResolution.le_orderAt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:28.021994+00:00
-- url     : https://prove2.me/theorems/12600659-3558-4b5d-aab6-da5073e42ee1
-- title:
--   Embedded Resolution: le order At iff
-- statement:
--   The Embedded Resolution construction uses the le order At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L188-L191

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

theorem FunctorialResolution.EmbeddedResolution.le_orderAt_iff (I : X.IdealSheafData) (x : X) (n : ℕ) :
    (n : ℕ∞) ≤ orderAt I x ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n := by sorry
