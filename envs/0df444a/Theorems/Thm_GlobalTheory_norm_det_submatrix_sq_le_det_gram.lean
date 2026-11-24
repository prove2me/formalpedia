-- Prove2me | Theorems.Thm_GlobalTheory_norm_det_submatrix_sq_le_det_gram
-- name    : GlobalTheory.norm_det_submatrix_sq_le_det_gram
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:12:16.403924+00:00
-- url     : https://prove2.me/theorems/7f51872d-70e5-4293-8b92-51042f699204
-- title:
--   Global Theory: norm det submatrix sq le det gram
-- statement:
--   The Global Theory construction uses the norm det submatrix sq le det gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/NormDetSubmatrixSqLeDetGram.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/NormDetSubmatrixSqLeDetGram.lean#L9-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDetAddEqDetMulDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormDetSubmatrixSqLeDetGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.norm_det_submatrix_sq_le_det_gram :
    ∀ (m : Type) [Fintype m] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix m ι ℂ)
      (e : ι → m), Function.Injective e →
        ‖(M.submatrix e id).det‖ ^ 2 ≤ (Mᴴ * M).det.re := by sorry
