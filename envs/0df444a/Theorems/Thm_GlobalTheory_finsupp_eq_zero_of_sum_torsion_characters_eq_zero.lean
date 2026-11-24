-- Prove2me | Theorems.Thm_GlobalTheory_finsupp_eq_zero_of_sum_torsion_characters_eq_zero
-- name    : GlobalTheory.finsupp_eq_zero_of_sum_torsion_characters_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:40.578058+00:00
-- url     : https://prove2.me/theorems/1e6b8d39-8115-47ac-bf1f-a40dbcd906f8
-- title:
--   Global Theory: finsupp eq zero of sum torsion characters eq zero
-- statement:
--   The Global Theory construction uses the finsupp eq zero of sum torsion characters eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinsuppEqZeroOfSumTorsionCharactersEqZero.lean#L41-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinsuppEqZeroOfSumTorsionCharactersEqZero.lean#L41-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinsuppEqZeroOfSumTorsionCharactersEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.finsupp_eq_zero_of_sum_torsion_characters_eq_zero :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k), 0 < N → IsPrimitiveRoot ζ N → ∀ (M : Type) [AddCommGroup M] [Module k M] (c : X →₀ M), (∀ α ∈ c.support, ∀ β ∈ c.support, (∃ w, α = β + N • w) → α = β) → (∀ t : Multiplicative X →* kˣ, t ^ N = 1 → c.sum (fun α m => (t (Multiplicative.ofAdd α) : k) • m) = 0) → c = 0 := by sorry
