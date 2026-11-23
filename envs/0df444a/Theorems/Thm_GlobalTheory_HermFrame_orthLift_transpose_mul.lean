-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_orthLift_transpose_mul
-- name    : GlobalTheory.HermFrame.orthLift_transpose_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:34.369079+00:00
-- url     : https://prove2.me/theorems/16408951-e1db-4347-a92c-1adf776b10d5
-- title:
--   Herm Frame: orth Lift transpose mul
-- statement:
--   The Herm Frame construction uses the orth Lift transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L385-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L385-L394

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

theorem GlobalTheory.HermFrame.orthLift_transpose_mul (hu : IsUnit (subGram H).det) :
    (orthLift H)ᵀ * H = fromCols 0 (quotGram H) := by sorry
