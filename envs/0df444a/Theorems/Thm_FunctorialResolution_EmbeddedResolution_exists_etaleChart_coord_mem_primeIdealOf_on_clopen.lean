-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_coord_mem_primeIdealOf_on_clopen
-- name    : FunctorialResolution.EmbeddedResolution.exists_etaleChart_coord_mem_primeIdealOf_on_clopen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:58:40.841724+00:00
-- url     : https://prove2.me/theorems/1c5c6209-ea1e-46e5-b910-f39a85db53bb
-- title:
--   Embedded Resolution: exists etale Chart coord mem prime Ideal Of on clopen
-- statement:
--   The Embedded Resolution construction uses the exists etale Chart coord mem prime Ideal Of on clopen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L429-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L429-L483

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
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
variable {W : Scheme.{u}} {k : Type u} [Field k]

theorem FunctorialResolution.EmbeddedResolution.exists_etaleChart_coord_mem_primeIdealOf_on_clopen (q : W ⟶ Spec (CommRingCat.of k)) [Smooth q]
    (E : List W.IdealSheafData) (_hE : InStrictNormalCrossingPosition q E) (Z : W.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith q Z E) (T : Z.subscheme.Opens)
    (_hTclosed : IsClosed (T : Set ↥Z.subscheme))
    (hcomp : ∀ D ∈ E, ∀ C ∈ irreducibleComponents ↥T.toScheme,
      ¬ ((T.ι ≫ Z.subschemeι).base '' C ⊆ (D.support : Set ↥W)))
    (y : ↥T.toScheme) :
    ∃ (U : T.toScheme.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (n : ℕ)
      (c : EtaleChart (T.ι ≫ (Z.subschemeι ≫ q)) U n) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < E.length,
        (γ i = none → restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = ⊤) ∧
          ∀ j, γ i = some j →
            restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = c.coordIdeal {j}) ∧
      (∀ i i', i < E.length → i' < E.length → ∀ j, γ i = some j → γ i' = some j → i = i') ∧
      (∀ i, i < E.length → ∀ j, γ i = some j → c.coord j ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) := by sorry
