-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_eq_of_perfect_of_dvd_sub
-- name    : GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:38.193704+00:00
-- url     : https://prove2.me/theorems/d95461e9-ffe4-45db-a424-7fcce54f9e7a
-- title:
--   Global Theory: ring Hom eq of perfect of dvd sub
-- statement:
--   The Global Theory construction uses the ring Hom eq of perfect of dvd sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RingHomEqOfPerfectOfDvdSubAdicSeparated.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RingHomEqOfPerfectOfDvdSubAdicSeparated.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomEqOfPerfectOfDvdSubAdicSeparated
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

theorem GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub :
    ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by sorry
