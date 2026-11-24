-- Prove2me | Theorems.Thm_GlobalTheory_ProjFrac_ev_resG
-- name    : GlobalTheory.ProjFrac.ev_resG
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:24.481486+00:00
-- url     : https://prove2.me/theorems/6885405d-d82c-4c62-8cfe-47d6befabf84
-- title:
--   Proj Frac: ev res G
-- statement:
--   The Proj Frac construction uses the ev res G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L33-L34

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

theorem GlobalTheory.ProjFrac.ev_resG {U V : (Proj 𝒜).Opens} (h : V ≤ U) (x : Proj 𝒜) (hx : x ∈ V) (s : Γ(Proj 𝒜, U)) :
    ev 𝒜 V x hx (resG (Proj 𝒜) h s) = ev 𝒜 U x (h hx) s := by sorry
