-- Prove2me | Theorems.Thm_GlobalTheory_entire_eq_of_mul_eq_mul_right
-- name    : GlobalTheory.entire_eq_of_mul_eq_mul_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:16:52.465796+00:00
-- url     : https://prove2.me/theorems/81ac9e8e-63b7-4894-96ad-bbfa27220b53
-- title:
--   Global Theory: entire eq of mul eq mul right
-- statement:
--   The Global Theory construction uses the entire eq of mul eq mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfThetaTranslateEqUnitMul.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfThetaTranslateEqUnitMul.lean#L17-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem GlobalTheory.entire_eq_of_mul_eq_mul_right {f₁ f₂ θ : E → ℂ} (h₁ : Differentiable ℂ f₁)
    (h₂ : Differentiable ℂ f₂) (hθ : Continuous θ) (hθ0 : θ ≠ 0)
    (h : ∀ z, f₁ z * θ z = f₂ z * θ z) : f₁ = f₂ := by sorry
