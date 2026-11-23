-- Prove2me | Theorems.Thm_GlobalTheory_Harm_sum_dite_lt
-- name    : GlobalTheory.Harm.sum_dite_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:44.205574+00:00
-- url     : https://prove2.me/theorems/08a8e3e6-7abe-42e3-9b12-d29b53ffddfe
-- title:
--   Harm: sum dite lt
-- statement:
--   The Harm construction uses the sum dite lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L132-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L132-L146

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

theorem GlobalTheory.Harm.sum_dite_lt {m p : ℕ} (hp : p ≤ m) (f : Fin p → ℤ) :
    ∑ k : Fin m, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) = ∑ k, f k := by sorry
