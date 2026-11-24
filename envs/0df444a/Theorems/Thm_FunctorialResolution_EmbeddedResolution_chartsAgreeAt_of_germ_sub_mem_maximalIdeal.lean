-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartsAgreeAt_of_germ_sub_mem_maximalIdeal
-- name    : FunctorialResolution.EmbeddedResolution.chartsAgreeAt_of_germ_sub_mem_maximalIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:34.382959+00:00
-- url     : https://prove2.me/theorems/ca141959-c82a-4d1c-9915-e05a9e677e65
-- title:
--   Embedded Resolution: charts Agree At of germ sub mem maximal Ideal
-- statement:
--   The Embedded Resolution construction uses the charts Agree At of germ sub mem maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L262-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean#L262-L280

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

theorem FunctorialResolution.EmbeddedResolution.chartsAgreeAt_of_germ_sub_mem_maximalIdeal (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V)
    (h : ∀ j : Fin n,
      (V.toScheme.presheaf.germ ⊤ (pointOfMem V p hp) (by trivial)).hom
          (c₁.coordTop j - c₂.coordTop j) ∈
        IsLocalRing.maximalIdeal (V.toScheme.presheaf.stalk (pointOfMem V p hp))) :
    ChartsAgreeAt c₁ c₂ p hp := by sorry
