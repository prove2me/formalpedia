-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_independent_mod_prime_of_pow_le_card
-- name    : GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:40.454008+00:00
-- url     : https://prove2.me/theorems/1111efe2-5233-4079-a96f-b842061a4441
-- title:
--   T: exists independent mod prime of pow le card
-- statement:
--   The T construction uses the exists independent mod prime of pow le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIndependentModPrimeOfPowLeCardStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIndependentModPrimeOfPowLeCardStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIndependentModPrimeOfPowLeCard
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIndependentModPrimeOfPowLeCardStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ) (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card → (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') → ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by sorry
