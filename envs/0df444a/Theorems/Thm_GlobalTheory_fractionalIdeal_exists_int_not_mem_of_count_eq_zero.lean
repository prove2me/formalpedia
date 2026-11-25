-- Prove2me | Theorems.Thm_GlobalTheory_fractionalIdeal_exists_int_not_mem_of_count_eq_zero
-- name    : GlobalTheory.fractionalIdeal_exists_int_not_mem_of_count_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:57.249479+00:00
-- url     : https://prove2.me/theorems/28436aee-9c48-45ac-9b3c-52f754c7a18d
-- title:
--   Global Theory: fractional Ideal exists int not mem of count eq zero
-- statement:
--   The Global Theory construction uses the fractional Ideal exists int not mem of count eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FractionalIdealExistsIntNotMemOfCountEqZero.lean#L6-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FractionalIdealExistsIntNotMemOfCountEqZero.lean#L6-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FractionalIdealExistsIntNotMemOfCountEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.fractionalIdeal_exists_int_not_mem_of_count_eq_zero
    {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (I : FractionalIdeal (nonZeroDivisors R) K) :
    I ≠ 0 → FractionalIdeal.count K v I = 0 → ∃ s : R, s ∉ v.asIdeal ∧ algebraMap R K s ∈ I := by sorry
