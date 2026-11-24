-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_incl_mul_orthProj_add
-- name    : GlobalTheory.HermFrame.incl_mul_orthProj_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:19.016958+00:00
-- url     : https://prove2.me/theorems/b2c520ff-b383-4b7e-9c64-552d66c09130
-- title:
--   Herm Frame: incl mul orth Proj add
-- statement:
--   The Herm Frame construction uses the incl mul orth Proj add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L371-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L371-L375

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

theorem GlobalTheory.HermFrame.incl_mul_orthProj_add (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    incl m l * orthProj H + orthLift H * quotMap m l = 1 := by sorry
