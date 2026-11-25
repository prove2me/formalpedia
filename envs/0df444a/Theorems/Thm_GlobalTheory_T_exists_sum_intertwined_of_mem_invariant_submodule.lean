-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_sum_intertwined_of_mem_invariant_submodule
-- name    : GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:08.709714+00:00
-- url     : https://prove2.me/theorems/d0b35dfb-7c32-43b9-a1e3-b98658bf309e
-- title:
--   T: exists sum intertwined of mem invariant submodule
-- statement:
--   The T construction uses the exists sum intertwined of mem invariant submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValuesStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValuesStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValuesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule : ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧ y = ∑ l, Sm l (q l) := by sorry
