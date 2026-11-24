-- Prove2me | Theorems.Thm_GlobalTheory_submodule_pow_simple_eq_sum_equiv_values
-- name    : GlobalTheory.submodule_pow_simple_eq_sum_equiv_values
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:17.393035+00:00
-- url     : https://prove2.me/theorems/b565c26e-9b14-41be-9b6b-b291291b4b76
-- title:
--   Global Theory: submodule pow simple eq sum equiv values
-- statement:
--   The Global Theory construction uses the submodule pow simple eq sum equiv values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean#L143-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean#L143-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory

theorem GlobalTheory.submodule_pow_simple_eq_sum_equiv_values :
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧
        y = ∑ l, Sm l (q l) := by sorry
