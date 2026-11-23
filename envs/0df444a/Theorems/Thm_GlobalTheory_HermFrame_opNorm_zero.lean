-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- name    : GlobalTheory.HermFrame.opNorm_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:00:02.352621+00:00
-- url     : https://prove2.me/theorems/3c267331-10c5-43c1-8ee6-be383cf3f82d
-- title:
--   Herm Frame: op Norm zero
-- statement:
--   The Herm Frame construction uses the op Norm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L181-L182

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

theorem GlobalTheory.HermFrame.opNorm_zero (H : Matrix m m ℂ) (K : Matrix n n ℂ) : opNorm H K 0 = 0 := by sorry
