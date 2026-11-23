-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_det_eq_det_subGram_mul
-- name    : GlobalTheory.HermFrame.det_eq_det_subGram_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:27.153663+00:00
-- url     : https://prove2.me/theorems/9092143a-d885-4250-bb28-4267f2ee75ef
-- title:
--   Herm Frame: det eq det sub Gram mul
-- statement:
--   The Herm Frame construction uses the det eq det sub Gram mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L408-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L408-L412

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

theorem GlobalTheory.HermFrame.det_eq_det_subGram_mul (hu : IsUnit (subGram H).det) :
    H.det = (subGram H).det * (quotGram H).det := by sorry
