-- Prove2me | Theorems.Thm_GlobalTheory_phiEq_dvd_all_pow
-- name    : GlobalTheory.phiEq_dvd_all_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:11.50258+00:00
-- url     : https://prove2.me/theorems/6b8f6c00-1052-44ad-98b5-a31e6b709849
-- title:
--   Global Theory: phi Eq dvd all pow
-- statement:
--   The Global Theory construction uses the phi Eq dvd all pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FrobeniusPowEquationDvdAllPow.lean#L42-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FrobeniusPowEquationDvdAllPow.lean#L42-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory

theorem GlobalTheory.phiEq_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R),
    ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R)
    (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) →
    (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by sorry
