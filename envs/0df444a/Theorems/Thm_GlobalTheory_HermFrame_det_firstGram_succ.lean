-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_det_firstGram_succ
-- name    : GlobalTheory.HermFrame.det_firstGram_succ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:45.016562+00:00
-- url     : https://prove2.me/theorems/a9c959e6-66bf-5c4f-aa7a-1ada64b4aa5c
-- title:
--   Herm Frame: det first Gram succ
-- statement:
--   The Herm Frame construction uses the det first Gram succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L474-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L474-L483

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
variable {N : ℕ}

theorem GlobalTheory.HermFrame.det_firstGram_succ (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (hu : IsUnit (firstGram i.2.le H).det) :
    (firstGram (k := i + 1) i.2 H).det = (firstGram i.2.le H).det * gradedGram H i () () := by sorry
