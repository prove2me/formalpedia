-- Prove2me | Theorems.Thm_GlobalTheory_exists_den_not_mem_of_count_eq_zero
-- name    : GlobalTheory.exists_den_not_mem_of_count_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:48.208969+00:00
-- url     : https://prove2.me/theorems/c95c7831-6fa8-5321-b988-0efb515678eb
-- title:
--   Global Theory: exists den not mem of count eq zero
-- statement:
--   The Global Theory construction uses the exists den not mem of count eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsDenNotMemOfCountEqZero.lean#L6-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsDenNotMemOfCountEqZero.lean#L6-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsDenNotMemOfCountEqZero
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

theorem GlobalTheory.exists_den_not_mem_of_count_eq_zero {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (P : IsDedekindDomain.HeightOneSpectrum R)
    (I : FractionalIdeal (nonZeroDivisors R) K) (hI : FractionalIdeal.count K P I = 0)
    {a : K} (ha : a ∈ I) :
    ∃ b c : R, c ∉ P.asIdeal ∧ algebraMap R K c * a = algebraMap R K b := by sorry
