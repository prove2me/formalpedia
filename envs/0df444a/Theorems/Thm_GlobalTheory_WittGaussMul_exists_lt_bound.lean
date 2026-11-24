-- Prove2me | Theorems.Thm_GlobalTheory_WittGaussMul_exists_lt_bound
-- name    : GlobalTheory.WittGaussMul.exists_lt_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:41.961804+00:00
-- url     : https://prove2.me/theorems/ff266bff-61d8-4760-913e-f86989081b97
-- title:
--   Witt Gauss Mul: exists lt bound
-- statement:
--   The Witt Gauss Mul construction uses the exists lt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormMul.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormMul.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.WittGaussMul

theorem GlobalTheory.WittGaussMul.exists_lt_bound (f : ℕ → ℝ) (B : ℝ) (hB : 0 < B) (i : ℕ) (h : ∀ k < i, f k < B) :
    ∃ c, 0 ≤ c ∧ c < B ∧ ∀ k < i, f k ≤ c := by sorry
