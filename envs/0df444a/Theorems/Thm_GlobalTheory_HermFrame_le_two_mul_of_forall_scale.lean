-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_le_two_mul_of_forall_scale
-- name    : GlobalTheory.HermFrame.le_two_mul_of_forall_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:57.923409+00:00
-- url     : https://prove2.me/theorems/9c9a0f4c-8e62-421f-ade9-4b47d7791be8
-- title:
--   Herm Frame: le two mul of forall scale
-- statement:
--   The Herm Frame construction uses the le two mul of forall scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L204-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L204-L222

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}

theorem GlobalTheory.HermFrame.le_two_mul_of_forall_scale {x c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ s, 0 < s → x ≤ c * (s * a ^ 2 + b ^ 2 / s)) : x ≤ 2 * c * a * b := by sorry
