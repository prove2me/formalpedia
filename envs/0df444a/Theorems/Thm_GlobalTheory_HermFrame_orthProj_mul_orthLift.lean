-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_orthProj_mul_orthLift
-- name    : GlobalTheory.HermFrame.orthProj_mul_orthLift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:26.318059+00:00
-- url     : https://prove2.me/theorems/7bf32d05-fc66-4fdb-9079-1dee2f810835
-- title:
--   Herm Frame: orth Proj mul orth Lift
-- statement:
--   The Herm Frame construction uses the orth Proj mul orth Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L362-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L362-L363

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
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem GlobalTheory.HermFrame.orthProj_mul_orthLift (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) : orthProj H * orthLift H = 0 := by sorry
