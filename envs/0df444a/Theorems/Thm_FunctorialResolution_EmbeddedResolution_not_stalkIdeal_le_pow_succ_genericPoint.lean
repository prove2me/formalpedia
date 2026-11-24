-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_not_stalkIdeal_le_pow_succ_genericPoint
-- name    : FunctorialResolution.EmbeddedResolution.not_stalkIdeal_le_pow_succ_genericPoint
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:57:55.497202+00:00
-- url     : https://prove2.me/theorems/9437a3a4-72d4-4567-9335-7357b000dfec
-- title:
--   Embedded Resolution: not stalk Ideal le pow succ generic Point
-- statement:
--   The Embedded Resolution construction uses the not stalk Ideal le pow succ generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L591-L604
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L591-L604

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

theorem FunctorialResolution.EmbeddedResolution.not_stalkIdeal_le_pow_succ_genericPoint (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C)
    (I : X.IdealSheafData) (a : ℕ) (ha : orderAt I hC.genericPoint = (a : ℕ∞)) :
    ¬ stalkIdeal I hC.genericPoint ≤ stalkIdeal D hC.genericPoint ^ (a + 1) := by sorry
