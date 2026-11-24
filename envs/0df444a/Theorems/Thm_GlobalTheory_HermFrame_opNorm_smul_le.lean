-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_opNorm_smul_le
-- name    : GlobalTheory.HermFrame.opNorm_smul_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:28.386281+00:00
-- url     : https://prove2.me/theorems/bf1dce88-d305-4d0f-949e-1614bcdd49f0
-- title:
--   Herm Frame: op Norm smul le
-- statement:
--   The Herm Frame construction uses the op Norm smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L191-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L191-L195

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

theorem GlobalTheory.HermFrame.opNorm_smul_le (hH : H.PosDef) (hK : K.PosSemidef) (c : ℂ) (T : Matrix n m ℂ) :
    opNorm H K (c • T) ≤ ‖c‖ * opNorm H K T := by sorry
