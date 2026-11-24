-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
-- name    : FunctorialResolution.EmbeddedResolution.mem_support_iff_stalkIdeal_le_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:48.707133+00:00
-- url     : https://prove2.me/theorems/0882bad4-026e-4a30-a8cb-3ff797c66182
-- title:
--   Embedded Resolution: mem support iff stalk Ideal le maximal Ideal
-- statement:
--   The Embedded Resolution construction uses the mem support iff stalk Ideal le maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L163-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L163-L173

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

theorem FunctorialResolution.EmbeddedResolution.mem_support_iff_stalkIdeal_le_maximalIdeal (I : X.IdealSheafData) (x : X) :
    x ∈ I.support ↔ stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by sorry
