-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ideal_le_pow_of_restrictIdeal_eq_coordIdeal
-- name    : FunctorialResolution.EmbeddedResolution.ideal_le_pow_of_restrictIdeal_eq_coordIdeal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:58:39.362881+00:00
-- url     : https://prove2.me/theorems/ae51244c-d8ca-4c18-8be5-888f5f20a110
-- title:
--   Embedded Resolution: ideal le pow of restrict Ideal eq coord Ideal
-- statement:
--   The Embedded Resolution construction uses the ideal le pow of restrict Ideal eq coord Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PowerContainmentAndOrderLocus.lean#L199-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PowerContainmentAndOrderLocus.lean#L199-L290

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
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

theorem FunctorialResolution.EmbeddedResolution.ideal_le_pow_of_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] {U : X.Opens}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (Z : X.IdealSheafData)
    (S : Finset (Fin n)) (h : restrictIdeal Z U = c.coordIdeal S) (m : ℕ)
    (I : X.IdealSheafData)
    (hord : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus I m) :
    I.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ ^ m := by sorry
