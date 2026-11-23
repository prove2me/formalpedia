-- Prove2me | Theorems.Thm_GlobalTheory_ProjFrac_awayToSection_mk
-- name    : GlobalTheory.ProjFrac.awayToSection_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:17.321482+00:00
-- url     : https://prove2.me/theorems/b18b3ca8-e61c-4c09-9607-6afe193d726a
-- title:
--   Proj Frac: away To Section mk
-- statement:
--   The Proj Frac construction uses the away To Section mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L224-L227

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

theorem GlobalTheory.ProjFrac.awayToSection_mk {f a : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (ha : a ∈ 𝒜 (n • d)) :
    (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      frac 𝒜 (Proj.basicOpen 𝒜 f) a (f ^ n) ha (SetLike.pow_mem_graded n hf)
        (fun x hx h => hx (x.isPrime.mem_of_pow_mem n h)) := by sorry
