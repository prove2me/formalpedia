-- Prove2me | Theorems.Thm_GlobalTheory_entire_eq_zero_of_mul_continuous_eq_zero
-- name    : GlobalTheory.entire_eq_zero_of_mul_continuous_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:48:56.926544+00:00
-- url     : https://prove2.me/theorems/e85d5378-9e79-47eb-be58-8e988a6b59f7
-- title:
--   Global Theory: entire eq zero of mul continuous eq zero
-- statement:
--   The Global Theory construction uses the entire eq zero of mul continuous eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TwoDvdMultiplierOfThetaZActEqUnitMul.lean#L16-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TwoDvdMultiplierOfThetaZActEqUnitMul.lean#L16-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TwoDvdMultiplierOfThetaZActEqUnitMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open Complex Matrix NumberField Filter Topology

theorem GlobalTheory.entire_eq_zero_of_mul_continuous_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f t : E → ℂ} (hf : Differentiable ℂ f) (ht : Continuous t) (ht0 : t ≠ 0)
    (h : ∀ z, f z * t z = 0) (z : E) : f z = 0 := by sorry
