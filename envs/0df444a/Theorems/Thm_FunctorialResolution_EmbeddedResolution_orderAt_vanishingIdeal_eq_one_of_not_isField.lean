-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_vanishingIdeal_eq_one_of_not_isField
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one_of_not_isField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:56.985731+00:00
-- url     : https://prove2.me/theorems/252ee862-2f6d-4f5e-895a-1bb29b89bc3f
-- title:
--   Embedded Resolution: order At vanishing Ideal eq one of not is Field
-- statement:
--   The Embedded Resolution construction uses the order At vanishing Ideal eq one of not is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L441-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L441-L447

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one_of_not_isField [IsLocallyNoetherian X]
    (Z : TopologicalSpace.Closeds X) (ξ : X) (T : Set X)
    (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T)
    (hξ : IsGenericPoint ξ T)
    (hfield : ¬ IsField (X.presheaf.stalk ξ)) :
    orderAt (Scheme.IdealSheafData.vanishingIdeal Z) ξ = 1 := by sorry
