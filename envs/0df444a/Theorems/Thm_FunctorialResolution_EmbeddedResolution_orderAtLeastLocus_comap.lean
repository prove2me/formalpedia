-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtLeastLocus_comap
-- name    : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_comap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:52:44.879717+00:00
-- url     : https://prove2.me/theorems/8979d654-0a2e-4457-8bf2-e440375eb203
-- title:
--   Embedded Resolution: order At Least Locus comap
-- statement:
--   The Embedded Resolution construction uses the order At Least Locus comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderPullback.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderPullback.lean#L96-L101

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_comap (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (I : X.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus (I.comap h) m = ⇑h.base ⁻¹' orderAtLeastLocus I m := by sorry
