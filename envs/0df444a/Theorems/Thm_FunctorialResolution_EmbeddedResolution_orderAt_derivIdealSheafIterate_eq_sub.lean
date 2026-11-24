-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_derivIdealSheafIterate_eq_sub
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_derivIdealSheafIterate_eq_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:14.557737+00:00
-- url     : https://prove2.me/theorems/5b9d6be7-1514-4d8d-b3cc-d8618fa09f2d
-- title:
--   Embedded Resolution: order At deriv Ideal Sheaf Iterate eq sub
-- statement:
--   The Embedded Resolution construction uses the order At deriv Ideal Sheaf Iterate eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafOrderDecrease.lean#L314-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafOrderDecrease.lean#L314-L337

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
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

theorem FunctorialResolution.EmbeddedResolution.orderAt_derivIdealSheafIterate_eq_sub (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (I : X.IdealSheafData)
    (x : X) {r : ℕ} (hr : orderAt I x = (r : ℕ∞)) {j : ℕ} (hj : j ≤ r) :
    orderAt (derivIdealSheafIterate k p j I) x = ((r - j : ℕ) : ℕ∞) := by sorry
