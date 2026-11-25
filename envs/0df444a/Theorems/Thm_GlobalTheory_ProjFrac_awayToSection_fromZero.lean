-- Prove2me | Theorems.Thm_GlobalTheory_ProjFrac_awayToSection_fromZero
-- name    : GlobalTheory.ProjFrac.awayToSection_fromZero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:58.758042+00:00
-- url     : https://prove2.me/theorems/543682d6-cbea-42f3-a107-953358e83134
-- title:
--   Proj Frac: away To Section from Zero
-- statement:
--   The Proj Frac construction uses the away To Section from Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L229-L231

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
open GlobalTheory GlobalTheory.ProjFrac
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {𝒜}

theorem GlobalTheory.ProjFrac.awayToSection_fromZero (f : A) (a : 𝒜 0) :
    (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ a) =
      frac 𝒜 (Proj.basicOpen 𝒜 f) a 1 a.2 (SetLike.one_mem_graded 𝒜) (by simp) := by sorry
