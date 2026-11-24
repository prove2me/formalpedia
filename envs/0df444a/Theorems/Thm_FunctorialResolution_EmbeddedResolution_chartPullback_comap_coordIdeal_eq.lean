-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullback_comap_coordIdeal_eq
-- name    : FunctorialResolution.EmbeddedResolution.chartPullback_comap_coordIdeal_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:48.620612+00:00
-- url     : https://prove2.me/theorems/d7613706-393d-4075-85dd-af990c8d872e
-- title:
--   Embedded Resolution: chart Pullback comap coord Ideal eq
-- statement:
--   The Embedded Resolution construction uses the chart Pullback comap coord Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L118-L122

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}

theorem FunctorialResolution.EmbeddedResolution.chartPullback_comap_coordIdeal_eq (c₁ c₂ : EtaleChart q V n) (S : Finset (Fin n)) :
    (c₁.coordIdeal S).comap (pullback.fst c₁.map c₂.map) =
      (c₂.coordIdeal S).comap (pullback.snd c₁.map c₂.map) := by sorry
