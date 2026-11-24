-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullbackFstStalkMap_eq
-- name    : FunctorialResolution.EmbeddedResolution.chartPullbackFstStalkMap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:57.059653+00:00
-- url     : https://prove2.me/theorems/a6fb0d59-341c-42fd-b0d6-3acc711e7902
-- title:
--   Embedded Resolution: chart Pullback Fst Stalk Map eq
-- statement:
--   The Embedded Resolution construction uses the chart Pullback Fst Stalk Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L303-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L303-L308

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

theorem FunctorialResolution.EmbeddedResolution.chartPullbackFstStalkMap_eq (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackFstStalkMap c₁ c₂ p hp h =
      eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
          (chartPullbackFst_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
        (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h) := by sorry
