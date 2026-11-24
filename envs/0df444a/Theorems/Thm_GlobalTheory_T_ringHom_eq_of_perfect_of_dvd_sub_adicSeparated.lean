-- Prove2me | Theorems.Thm_GlobalTheory_T_ringHom_eq_of_perfect_of_dvd_sub_adicSeparated
-- name    : GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:56:26.699502+00:00
-- url     : https://prove2.me/theorems/3939341c-665c-49f7-bfdc-7f42d9dc985b
-- title:
--   T: ring Hom eq of perfect of dvd sub adic Separated
-- statement:
--   The T construction uses the ring Hom eq of perfect of dvd sub adic Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RingHomEqOfPerfectOfDvdSubAdicSeparatedStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RingHomEqOfPerfectOfDvdSubAdicSeparatedStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomEqOfPerfectOfDvdSubAdicSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomEqOfPerfectOfDvdSubAdicSeparatedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by sorry
