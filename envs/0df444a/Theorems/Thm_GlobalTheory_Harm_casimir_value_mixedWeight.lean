-- Prove2me | Theorems.Thm_GlobalTheory_Harm_casimir_value_mixedWeight
-- name    : GlobalTheory.Harm.casimir_value_mixedWeight
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:26.852507+00:00
-- url     : https://prove2.me/theorems/9127efe8-de65-4113-8986-b287e89a0818
-- title:
--   Harm: casimir value mixed Weight
-- statement:
--   The Harm construction uses the casimir value mixed Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L173-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L173-L198

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

theorem GlobalTheory.Harm.casimir_value_mixedWeight {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k : Fin m, _root_.GlobalTheory.Harm.mixedWeight m a b k * (_root_.GlobalTheory.Harm.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((m : ℤ) - p) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin q, (b i : ℤ) * (b i + q - 1 - 2 * (i : ℕ)) + ((m : ℤ) - q) * ∑ i, (b i : ℤ)) := by sorry
