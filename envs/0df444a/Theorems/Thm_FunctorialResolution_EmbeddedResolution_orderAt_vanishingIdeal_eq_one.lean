-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_vanishingIdeal_eq_one
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:47.397674+00:00
-- url     : https://prove2.me/theorems/cd49ab0c-32ec-45a0-ae3f-86329f839a32
-- title:
--   Embedded Resolution: order At vanishing Ideal eq one
-- statement:
--   The Embedded Resolution construction uses the order At vanishing Ideal eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L429-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L429-L435

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one [IsLocallyNoetherian X] (Z : TopologicalSpace.Closeds X)
    (ξ : X) (T : Set X) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T)
    (hne : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ≠ ⊥) :
    orderAt (Scheme.IdealSheafData.vanishingIdeal Z) ξ = 1 := by sorry
