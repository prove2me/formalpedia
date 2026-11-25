-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_opNorm_mul_le
-- name    : GlobalTheory.HermFrame.opNorm_mul_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:09.479924+00:00
-- url     : https://prove2.me/theorems/67a92ea3-7729-449e-b6b1-2810d3104588
-- title:
--   Herm Frame: op Norm mul le
-- statement:
--   The Herm Frame construction uses the op Norm mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L197-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L197-L202

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

theorem GlobalTheory.HermFrame.opNorm_mul_le (hH : H.PosDef) (hK : K.PosDef) (hL : L.PosSemidef) (S : Matrix l n ℂ)
    (T : Matrix n m ℂ) : opNorm H L (S * T) ≤ opNorm K L S * opNorm H K T := by sorry
