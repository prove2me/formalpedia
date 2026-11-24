-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullbackFst_comp_eq_chartPullbackSnd_comp
-- name    : FunctorialResolution.EmbeddedResolution.chartPullbackFst_comp_eq_chartPullbackSnd_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:11.630135+00:00
-- url     : https://prove2.me/theorems/e4bc31a1-5af1-4da4-be39-7ea78fffb1d7
-- title:
--   Embedded Resolution: chart Pullback Fst comp eq chart Pullback Snd comp
-- statement:
--   The Embedded Resolution construction uses the chart Pullback Fst comp eq chart Pullback Snd comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L109-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L109-L116

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

theorem FunctorialResolution.EmbeddedResolution.chartPullbackFst_comp_eq_chartPullbackSnd_comp (c₁ c₂ : EtaleChart q V n) :
    chartPullbackFst c₁ c₂ ≫ q = chartPullbackSnd c₁ c₂ ≫ q := by sorry
