-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_mdel_inv
-- name    : GlobalTheory.HermFrame.mdel_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:00.466701+00:00
-- url     : https://prove2.me/theorems/6486cbf3-cfcb-433f-ae7c-ec30cc5f04b4
-- title:
--   Herm Frame: mdel inv
-- statement:
--   The Herm Frame construction uses the mdel inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L231-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExtFormAdjEqNegSecondForm.lean#L231-L237

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable {A B : E → Matrix m n ℂ} {z : E} {j k : WithTop ℕ∞}

theorem GlobalTheory.HermFrame.mdel_inv [Fintype n] [DecidableEq n] {A : E → Matrix n n ℂ} (h : MContDiffAt 1 A z)
    (hu : IsUnit (A z).det) (ξ : E) :
    mdel (fun x => (A x)⁻¹) z ξ = -((A z)⁻¹ * mdel A z ξ * (A z)⁻¹) := by sorry
