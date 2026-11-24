-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_stalkIdeal_vanishingIdeal_eq
-- name    : FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.stalkIdeal_vanishingIdeal_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:58:42.563156+00:00
-- url     : https://prove2.me/theorems/57cabb9c-0891-4fbf-8c58-34237892d9b8
-- title:
--   Is Irreducible Component Of Support: stalk Ideal vanishing Ideal eq
-- statement:
--   The Is Irreducible Component Of Support construction uses the stalk Ideal vanishing Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean#L409-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean#L409-L417

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
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
open FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
variable {k : Type u} [Field k]

theorem FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.stalkIdeal_vanishingIdeal_eq [TopologicalSpace.NoetherianSpace ↥X]
    (hC : IsIrreducibleComponentOfSupport D C) (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ C) :
    stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = stalkIdeal D x := by sorry
