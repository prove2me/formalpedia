-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_exists_affineOpen_etaleChart_coordIdeal
-- name    : FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.exists_affineOpen_etaleChart_coordIdeal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:55:47.519368+00:00
-- url     : https://prove2.me/theorems/d9907a66-7888-4aee-96fb-ee3bf1e814c8
-- title:
--   Is Irreducible Component Of Support: exists affine Open etale Chart coord Ideal
-- statement:
--   The Is Irreducible Component Of Support construction uses the exists affine Open etale Chart coord Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean#L342-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IrreducibleComponentsOfSupport.lean#L342-L407

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

theorem FunctorialResolution.EmbeddedResolution.IsIrreducibleComponentOfSupport.exists_affineOpen_etaleChart_coordIdeal [TopologicalSpace.NoetherianSpace ↥X] (hC : IsIrreducibleComponentOfSupport D C)
    (p : X ⟶ Spec (CommRingCat.of k))
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ C) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (n : ℕ) (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧
      (∀ y : X, y ∈ V → y ∈ (D.support : Set X) → y ∈ C) ∧
      (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal ⟨V, hV⟩ = D.ideal ⟨V, hV⟩ ∧
      (∀ W : X.affineOpens, (↑W : X.Opens) ≤ V →
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal W = D.ideal W) ∧
      (∀ y : X, y ∈ V →
        stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) y = stalkIdeal D y) := by sorry
