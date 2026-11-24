-- Prove2me | Theorems.Thm_GlobalTheory_bounded_powers_or_exists_valuationSubring_dvd
-- name    : GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:07:20.479044+00:00
-- url     : https://prove2.me/theorems/e602c743-4c22-43b4-baf6-86f63d836049
-- title:
--   Global Theory: bounded powers or exists valuation Subring dvd
-- statement:
--   The Global Theory construction uses the bounded powers or exists valuation Subring dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BoundedPowersOrExistsValuationSubringDvd.lean#L34-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BoundedPowersOrExistsValuationSubringDvd.lean#L34-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BoundedPowersOrExistsValuationSubringDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open Polynomial
open GlobalTheory

theorem GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd :
    ∀ (R : Type) [CommRing R] (u x : R) (M : ℕ), u ∈ nonZeroDivisors R →
      (∀ r, IsUnit (1 - u * r)) →
      (∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n) ∨
        ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L)
          (f : R →+* ↥V), f u ≠ 0 ∧ ¬ IsUnit (f u) ∧ f x ∣ f u ^ M := by sorry
