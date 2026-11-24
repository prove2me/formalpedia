-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint
-- name    : FunctorialResolution.EmbeddedResolution.stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:15.938821+00:00
-- url     : https://prove2.me/theorems/f993fa90-a0e3-4f23-882d-6ab54b0e3c29
-- title:
--   Embedded Resolution: stalk Ideal vanishing Ideal eq maximal Ideal of is Generic Point
-- statement:
--   The Embedded Resolution construction uses the stalk Ideal vanishing Ideal eq maximal Ideal of is Generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L353-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L353-L427

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

theorem FunctorialResolution.EmbeddedResolution.stalkIdeal_vanishingIdeal_eq_maximalIdeal_of_isGenericPoint (Z : TopologicalSpace.Closeds X) (ξ : X)
    (T : Set X) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T) :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal Z) ξ
      = IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by sorry
