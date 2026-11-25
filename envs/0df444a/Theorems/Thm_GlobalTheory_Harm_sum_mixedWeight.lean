-- Prove2me | Theorems.Thm_GlobalTheory_Harm_sum_mixedWeight
-- name    : GlobalTheory.Harm.sum_mixedWeight
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:09.741112+00:00
-- url     : https://prove2.me/theorems/5033aaee-b8fe-45a4-9d07-3614ca18c2c8
-- title:
--   Harm: sum mixed Weight
-- statement:
--   The Harm construction uses the sum mixed Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L161-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L161-L169

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

theorem GlobalTheory.Harm.sum_mixedWeight {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k, _root_.GlobalTheory.Harm.mixedWeight m a b k = ∑ i, (a i : ℤ) - ∑ i, (b i : ℤ) := by sorry
