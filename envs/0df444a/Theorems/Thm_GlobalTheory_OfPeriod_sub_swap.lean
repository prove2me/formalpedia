-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_sub_swap
-- name    : GlobalTheory.OfPeriod.sub_swap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:18.688452+00:00
-- url     : https://prove2.me/theorems/5ab82a29-35c1-4f86-9412-3a946aae5dac
-- title:
--   Of Period: sub swap
-- statement:
--   The Of Period construction uses the sub swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L167-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L167-L183

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
variable (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
  (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) {b : W →ₗ[ℝ] W} (hb : ∀ w, b w ∈ R)
  (hb' : ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im)
variable {O : Type} [CommRing O] [StarRing O] {ρ : O →+* Module.End ℂ W}
  (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w)) (hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R)
omit [IsScalarTower ℝ ℂ W]
include hconj hR hb

theorem GlobalTheory.OfPeriod.sub_swap {w w' u u' : W} (hu : ∀ r ∈ R, S u r = 0) (hu' : ∀ r ∈ R, S u' r = 0)
    (h : w = b (I • w) + I • b w + u) (h' : w' = b (I • w') + I • b w' + u') :
    S w (b w') - S u u' / (2 * I) = S w' (b w) - S u' u / (2 * I) - (S w w').im := by sorry
