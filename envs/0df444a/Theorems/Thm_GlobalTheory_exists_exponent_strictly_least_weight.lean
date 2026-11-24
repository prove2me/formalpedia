-- Prove2me | Theorems.Thm_GlobalTheory_exists_exponent_strictly_least_weight
-- name    : GlobalTheory.exists_exponent_strictly_least_weight
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:35.823805+00:00
-- url     : https://prove2.me/theorems/d80000ac-c2f9-48a7-b2fb-176a93836337
-- title:
--   Global Theory: exists exponent strictly least weight
-- statement:
--   The Global Theory construction uses the exists exponent strictly least weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsExponentStrictlyLeastWeight.lean#L9-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsExponentStrictlyLeastWeight.lean#L9-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsExponentStrictlyLeastWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open scoped BigOperators

theorem GlobalTheory.exists_exponent_strictly_least_weight :
    ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ,
      (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) →
        ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by sorry
