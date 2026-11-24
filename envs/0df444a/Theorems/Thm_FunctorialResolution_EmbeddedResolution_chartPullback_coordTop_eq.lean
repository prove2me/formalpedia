-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullback_coordTop_eq
-- name    : FunctorialResolution.EmbeddedResolution.chartPullback_coordTop_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:24.265805+00:00
-- url     : https://prove2.me/theorems/1001fd6d-c5e3-4eb6-9207-fbf7432c94fc
-- title:
--   Embedded Resolution: chart Pullback coord Top eq
-- statement:
--   The Embedded Resolution construction uses the chart Pullback coord Top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L100-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L100-L107

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

theorem FunctorialResolution.EmbeddedResolution.chartPullback_coordTop_eq (c₁ c₂ : EtaleChart q V n) (j : Fin n) :
    (pullback.fst c₁.map c₂.map).appTop.hom (c₁.coordTop j) =
      (pullback.snd c₁.map c₂.map).appTop.hom (c₂.coordTop j) := by sorry
