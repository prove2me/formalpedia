-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unit_frobenius_iterate_product_eq
-- name    : GlobalTheory.T.exists_unit_frobenius_iterate_product_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:42.448208+00:00
-- url     : https://prove2.me/theorems/553b663f-88fc-4c1d-bf8f-98472854ce93
-- title:
--   T: exists unit frobenius iterate product eq
-- statement:
--   The T construction uses the exists unit frobenius iterate product eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitFrobeniusIterateProductEqStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitFrobeniusIterateProductEqStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitFrobeniusIterateProductEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitFrobeniusIterateProductEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unit_frobenius_iterate_product_eq : ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A → ∀ (φ : A →+* A) (u : A), IsUnit u → (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) → ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by sorry
