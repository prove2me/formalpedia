-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_least_weight_exponent
-- name    : GlobalTheory.T.exists_least_weight_exponent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:01.258941+00:00
-- url     : https://prove2.me/theorems/d83bf482-e2ba-4c71-8e5b-0d5aaf39460b
-- title:
--   T: exists least weight exponent
-- statement:
--   The T construction uses the exists least weight exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsExponentStrictlyLeastWeightStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsExponentStrictlyLeastWeightStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsExponentStrictlyLeastWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsExponentStrictlyLeastWeightStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_least_weight_exponent : ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ, (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) → ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by sorry
