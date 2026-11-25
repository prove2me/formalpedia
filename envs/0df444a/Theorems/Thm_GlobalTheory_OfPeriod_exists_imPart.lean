-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_exists_imPart
-- name    : GlobalTheory.OfPeriod.exists_imPart
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:21.122069+00:00
-- url     : https://prove2.me/theorems/a36b8a19-08ea-4926-a9e2-b870c7c7c372
-- title:
--   Of Period: exists im Part
-- statement:
--   The Of Period construction uses the exists im Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L60-L74

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

theorem GlobalTheory.OfPeriod.exists_imPart [FiniteDimensional ℝ W] (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) :
    ∃ b : W →ₗ[ℝ] W, (∀ w, b w ∈ R) ∧ ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im := by sorry
