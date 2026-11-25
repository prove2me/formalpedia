-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
-- name    : GlobalTheory.OfPeriod.reForm_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:36.60669+00:00
-- url     : https://prove2.me/theorems/ed44e009-85fb-4c67-ba06-0d53a93d5b8c
-- title:
--   Of Period: re Form apply
-- statement:
--   The Of Period construction uses the re Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L50-L50

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

theorem GlobalTheory.OfPeriod.reForm_apply (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x y : W) : reForm S x y = (S x y).re := by sorry

attribute [defeq] GlobalTheory.OfPeriod.reForm_apply
