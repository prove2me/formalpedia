-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_gnorm_sq
-- name    : GlobalTheory.HermFrame.gnorm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:05.723261+00:00
-- url     : https://prove2.me/theorems/c8e012c6-d17a-4ec7-970c-7bd73949752f
-- title:
--   Herm Frame: gnorm sq
-- statement:
--   The Herm Frame construction uses the gnorm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L97-L98

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

theorem GlobalTheory.HermFrame.gnorm_sq {H : Matrix n n ℂ} (hH : H.PosSemidef) (v : n → ℂ) :
    gnorm H v ^ 2 = (form H v v).re := by sorry
