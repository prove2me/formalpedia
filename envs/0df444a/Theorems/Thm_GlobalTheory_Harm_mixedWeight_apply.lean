-- Prove2me | Theorems.Thm_GlobalTheory_Harm_mixedWeight_apply
-- name    : GlobalTheory.Harm.mixedWeight_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:43.712546+00:00
-- url     : https://prove2.me/theorems/0f594588-820e-4395-a56a-ca5b0a1eeb45
-- title:
--   Harm: mixed Weight apply
-- statement:
--   The Harm construction uses the mixed Weight apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L108-L111

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

theorem GlobalTheory.Harm.mixedWeight_apply (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) (k : Fin m) :
    mixedWeight m a b k =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
        (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) := by sorry
