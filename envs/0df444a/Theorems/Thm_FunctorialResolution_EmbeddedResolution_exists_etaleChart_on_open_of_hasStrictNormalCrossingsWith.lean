-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith
-- name    : FunctorialResolution.EmbeddedResolution.exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:58:15.631279+00:00
-- url     : https://prove2.me/theorems/66e6087f-bf2e-407e-8377-d490306d01e2
-- title:
--   Embedded Resolution: exists etale Chart on open of has Strict Normal Crossings With
-- statement:
--   The Embedded Resolution construction uses the exists etale Chart on open of has Strict Normal Crossings With property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L338-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L338-L427

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

theorem FunctorialResolution.EmbeddedResolution.exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith (q : W ⟶ Spec (CommRingCat.of k))
    (E : List W.IdealSheafData) (Z : W.IdealSheafData) (hZ : HasStrictNormalCrossingsWith q Z E)
    (T : Z.subscheme.Opens)
    (hcomp : ∀ D ∈ E, ∀ C ∈ irreducibleComponents ↥T.toScheme,
      ¬ ((T.ι ≫ Z.subschemeι).base '' C ⊆ (D.support : Set ↥W)))
    (y : ↥T.toScheme) :
    ∃ (U : T.toScheme.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (n : ℕ)
      (c : EtaleChart (T.ι ≫ (Z.subschemeι ≫ q)) U n) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < E.length,
        (γ i = none → restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = ⊤) ∧
          ∀ j, γ i = some j →
            restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = c.coordIdeal {j}) ∧
      (∀ i i', i < E.length → i' < E.length → ∀ j, γ i = some j → γ i' = some j → i = i') := by sorry
