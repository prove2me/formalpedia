-- Prove2me | Theorems.Thm_GlobalTheory_Harm_sum_filter_lt_eq_sum_range
-- name    : GlobalTheory.Harm.sum_filter_lt_eq_sum_range
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:15.378825+00:00
-- url     : https://prove2.me/theorems/ac40d0ef-89a5-480d-90a3-7cba9283e43f
-- title:
--   Harm: sum filter lt eq sum range
-- statement:
--   The Harm construction uses the sum filter lt eq sum range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L9-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
open Finset

theorem GlobalTheory.Harm.sum_filter_lt_eq_sum_range {m : ℕ} (f : Fin m → ℤ) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), f k =
      ∑ j ∈ range i, if h : j < m then f ⟨j, h⟩ else 0 := by sorry
