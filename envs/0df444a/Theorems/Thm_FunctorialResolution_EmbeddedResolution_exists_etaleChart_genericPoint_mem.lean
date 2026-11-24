-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_genericPoint_mem
-- name    : FunctorialResolution.EmbeddedResolution.exists_etaleChart_genericPoint_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:03:00.417994+00:00
-- url     : https://prove2.me/theorems/59cf9006-923b-455b-9be8-2506eea01e1b
-- title:
--   Embedded Resolution: exists etale Chart generic Point mem
-- statement:
--   The Embedded Resolution construction uses the exists etale Chart generic Point mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L488-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L488-L563

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

theorem FunctorialResolution.EmbeddedResolution.exists_etaleChart_genericPoint_mem (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C)
    (x : X) (hx : x ∈ C) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (hη : hC.genericPoint ∈ V) (n : ℕ)
      (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧ hC.genericPoint ⤳ x ∧
        hC.genericPoint ∈ D.support ∧
        ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
          P ≤ (hV.primeIdealOf ⟨hC.genericPoint, hη⟩).asIdeal →
          P = (hV.primeIdealOf ⟨hC.genericPoint, hη⟩).asIdeal := by sorry
