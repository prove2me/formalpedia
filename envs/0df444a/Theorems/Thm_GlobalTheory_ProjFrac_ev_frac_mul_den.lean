-- Prove2me | Theorems.Thm_GlobalTheory_ProjFrac_ev_frac_mul_den
-- name    : GlobalTheory.ProjFrac.ev_frac_mul_den
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:19.19281+00:00
-- url     : https://prove2.me/theorems/27a335c2-b268-44ca-a9bf-d8d94e84a6b7
-- title:
--   Proj Frac: ev frac mul den
-- statement:
--   The Proj Frac construction uses the ev frac mul den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean#L59-L62

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
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b} {hU' : U ≤ Proj.basicOpen 𝒜 b'}

theorem GlobalTheory.ProjFrac.ev_frac_mul_den (x : Proj 𝒜) (hx : x ∈ U) :
    ev 𝒜 U x hx (frac 𝒜 U a b ha hb hU) * algebraMap A _ b = algebraMap A _ a := by sorry
