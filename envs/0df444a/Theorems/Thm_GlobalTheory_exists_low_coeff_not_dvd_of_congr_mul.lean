-- Prove2me | Theorems.Thm_GlobalTheory_exists_low_coeff_not_dvd_of_congr_mul
-- name    : GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:15.346002+00:00
-- url     : https://prove2.me/theorems/7ca5a1a4-e59d-4df2-8d09-0179798ca71f
-- title:
--   Global Theory: exists low coeff not dvd of congr mul
-- statement:
--   The Global Theory construction uses the exists low coeff not dvd of congr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLowCoeffNotDvdOfCongrMul.lean#L12-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLowCoeffNotDvdOfCongrMul.lean#L12-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLowCoeffNotDvdOfCongrMul
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
open PowerSeries
open scoped BigOperators
open PowerSeries

theorem GlobalTheory.exists_low_coeff_not_dvd_of_congr_mul : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (D g f : PowerSeries O) (m₀ v nT MT : ℕ), (∃ m ≤ m₀, IsUnit (PowerSeries.coeff m D)) → ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff 0 g → v + 1 ≤ nT → (v + 1) * m₀ ≤ MT → (∀ i ≤ MT, ϖ ^ nT ∣ PowerSeries.coeff i (f - D * g)) → ∃ i ≤ (v + 1) * m₀, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff i f := by sorry
