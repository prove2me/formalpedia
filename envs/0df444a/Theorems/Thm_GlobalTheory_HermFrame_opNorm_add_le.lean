-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_opNorm_add_le
-- name    : GlobalTheory.HermFrame.opNorm_add_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:18.618508+00:00
-- url     : https://prove2.me/theorems/8c354aa8-5d60-4849-bd40-fd5cbb92487f
-- title:
--   Herm Frame: op Norm add le
-- statement:
--   The Herm Frame construction uses the op Norm add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L184-L189

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

theorem GlobalTheory.HermFrame.opNorm_add_le (hH : H.PosDef) (hK : K.PosSemidef) (S T : Matrix n m ℂ) :
    opNorm H K (S + T) ≤ opNorm H K S + opNorm H K T := by sorry
