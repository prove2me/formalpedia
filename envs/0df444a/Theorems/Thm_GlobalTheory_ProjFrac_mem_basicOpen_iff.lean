-- Prove2me | Theorems.Thm_GlobalTheory_ProjFrac_mem_basicOpen_iff
-- name    : GlobalTheory.ProjFrac.mem_basicOpen_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:33.031236+00:00
-- url     : https://prove2.me/theorems/92660ad3-b64e-4d2c-8563-8840b87f9854
-- title:
--   Proj Frac: mem basic Open iff
-- statement:
--   The Proj Frac construction uses the mem basic Open iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L36-L42

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

theorem GlobalTheory.ProjFrac.mem_basicOpen_iff {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    x ∈ (Proj 𝒜).basicOpen s ↔ IsUnit (ev 𝒜 U x hx s) := by sorry
