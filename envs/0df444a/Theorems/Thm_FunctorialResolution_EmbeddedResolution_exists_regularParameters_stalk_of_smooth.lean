-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_regularParameters_stalk_of_smooth
-- name    : FunctorialResolution.EmbeddedResolution.exists_regularParameters_stalk_of_smooth
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:33:29.678938+00:00
-- url     : https://prove2.me/theorems/727109c8-d458-477c-a883-88808a5a6475
-- title:
--   Embedded Resolution: exists regular Parameters stalk of smooth
-- statement:
--   The Embedded Resolution construction uses the exists regular Parameters stalk of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtMultiplicativity.lean#L130-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtMultiplicativity.lean#L130-L161

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AdaptedParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
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

theorem FunctorialResolution.EmbeddedResolution.exists_regularParameters_stalk_of_smooth (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    letI := stalkAlgebra k p x
    ∃ (h : ℕ) (y : Fin h → X.presheaf.stalk x)
      (D : Fin h → Derivation k (X.presheaf.stalk x) (X.presheaf.stalk x)),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (∀ i j : Fin h, D i (y j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin h, ∀ a : X.presheaf.stalk x, D i (D j a) = D j (D i a)) := by sorry
