-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_coord_notMem_maximalIdeal_sq
-- name    : FunctorialResolution.EmbeddedResolution.germ_coord_notMem_maximalIdeal_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:45:55.093888+00:00
-- url     : https://prove2.me/theorems/8876d92f-278e-488c-873a-c35b167325f7
-- title:
--   Embedded Resolution: germ coord not Mem maximal Ideal sq
-- statement:
--   The Embedded Resolution construction uses the germ coord not Mem maximal Ideal sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/CoordinateIdealOrderOne.lean#L27-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/CoordinateIdealOrderOne.lean#L27-L69

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_CoordinateIdealOrderOne
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

theorem FunctorialResolution.EmbeddedResolution.germ_coord_notMem_maximalIdeal_sq {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (y : X) (hy : y ∈ V)
    (hmem : c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) :
    (X.presheaf.germ V y hy).hom (c.coord j) ∉
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ 2 := by sorry
