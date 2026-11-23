-- Prove2me | Theorems.Thm_GlobalTheory_Harm_sum_dite_rev_lt
-- name    : GlobalTheory.Harm.sum_dite_rev_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:57.834541+00:00
-- url     : https://prove2.me/theorems/90f981b9-be9e-47ff-aad9-5df567d28771
-- title:
--   Harm: sum dite rev lt
-- statement:
--   The Harm construction uses the sum dite rev lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L150-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L150-L157

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

theorem GlobalTheory.Harm.sum_dite_rev_lt {m q : ℕ} (hq : q ≤ m) (f : Fin q → ℤ) :
    ∑ k : Fin m, (if h : m - 1 - (k : ℕ) < q then f ⟨m - 1 - k, h⟩ else 0) = ∑ k, f k := by sorry
