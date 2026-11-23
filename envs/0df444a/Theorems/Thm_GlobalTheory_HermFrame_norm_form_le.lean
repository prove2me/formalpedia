-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_norm_form_le
-- name    : GlobalTheory.HermFrame.norm_form_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:01.056794+00:00
-- url     : https://prove2.me/theorems/1e4f60cb-37cb-49ce-bcb6-0892bb8d43ea
-- title:
--   Herm Frame: norm form le
-- statement:
--   The Herm Frame construction uses the norm form le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L110-L113

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

theorem GlobalTheory.HermFrame.norm_form_le {H : Matrix n n ℂ} (hH : H.PosSemidef) (v w : n → ℂ) :
    ‖form H v w‖ ≤ gnorm H v * gnorm H w := by sorry
