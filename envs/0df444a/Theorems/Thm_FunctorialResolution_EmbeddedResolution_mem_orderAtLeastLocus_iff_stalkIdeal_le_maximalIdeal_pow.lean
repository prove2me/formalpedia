-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow
-- name    : FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:46.766703+00:00
-- url     : https://prove2.me/theorems/1d576ef3-73ee-4f79-86d0-01259fd3a3fc
-- title:
--   Embedded Resolution: mem order At Least Locus iff stalk Ideal le maximal Ideal pow
-- statement:
--   The Embedded Resolution construction uses the mem order At Least Locus iff stalk Ideal le maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L549-L553
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L549-L553

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

theorem FunctorialResolution.EmbeddedResolution.mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow (I : X.IdealSheafData) (m : ℕ)
    (x : X) :
    x ∈ orderAtLeastLocus I m ↔
      stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ m := by sorry
