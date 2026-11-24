-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:30.836894+00:00
-- url     : https://prove2.me/theorems/dbd12b06-1215-4570-a9c1-ff02c89cbc19
-- title:
--   Embedded Resolution: order At eq one of stalk Ideal eq maximal Ideal
-- statement:
--   The Embedded Resolution construction uses the order At eq one of stalk Ideal eq maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L290-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L290-L307

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (h : stalkIdeal I x = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hne : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≠ ⊥) :
    orderAt I x = 1 := by sorry
