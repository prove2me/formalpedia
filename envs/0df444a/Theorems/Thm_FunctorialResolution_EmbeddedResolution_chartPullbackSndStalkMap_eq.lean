-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullbackSndStalkMap_eq
-- name    : FunctorialResolution.EmbeddedResolution.chartPullbackSndStalkMap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:21:16.30247+00:00
-- url     : https://prove2.me/theorems/23134cf6-976e-4a95-bad1-ff3c15248f44
-- title:
--   Embedded Resolution: chart Pullback Snd Stalk Map eq
-- statement:
--   The Embedded Resolution construction uses the chart Pullback Snd Stalk Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L310-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L310-L315

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

theorem FunctorialResolution.EmbeddedResolution.chartPullbackSndStalkMap_eq (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackSndStalkMap c₁ c₂ p hp h =
      eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
          (chartPullbackSnd_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
        (chartPullbackSnd c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h) := by sorry
