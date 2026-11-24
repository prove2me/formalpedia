-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:52:35.507228+00:00
-- url     : https://prove2.me/theorems/f6e54513-37a7-43eb-b7cd-f1782732e97f
-- title:
--   Embedded Resolution: order At eq zero or le order At of is Deriv Balanced
-- statement:
--   The Embedded Resolution construction uses the order At eq zero or le order At of is Deriv Balanced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivBalancedOrderLocus.lean#L17-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivBalancedOrderLocus.lean#L17-L46

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivBalancedOrderLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
  (I : X.IdealSheafData) (m : ℕ)

theorem FunctorialResolution.EmbeddedResolution.orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) (x : X) :
    orderAt I x = 0 ∨ (m : ℕ∞) ≤ orderAt I x := by sorry
