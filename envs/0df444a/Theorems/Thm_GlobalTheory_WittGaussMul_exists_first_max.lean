-- Prove2me | Theorems.Thm_GlobalTheory_WittGaussMul_exists_first_max
-- name    : GlobalTheory.WittGaussMul.exists_first_max
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:21.370561+00:00
-- url     : https://prove2.me/theorems/c13a5fd8-dd9f-49b0-8521-42d0381b6a4f
-- title:
--   Witt Gauss Mul: exists first max
-- statement:
--   The Witt Gauss Mul construction uses the exists first max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormMul.lean#L20-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormMul.lean#L20-L40

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

theorem GlobalTheory.WittGaussMul.exists_first_max (f : ℕ → ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hf : ∀ n, f n ≤ r ^ n) (hpos : 0 < ⨆ n, f n) :
    ∃ i, f i = (⨆ n, f n) ∧ ∀ k < i, f k < ⨆ n, f n := by sorry
