-- Prove2me | Theorems.Thm_GlobalTheory_finite_and_ncard_setOf_index_pi_le
-- name    : GlobalTheory.finite_and_ncard_setOf_index_pi_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:33.154819+00:00
-- url     : https://prove2.me/theorems/3609cb60-4950-436e-981d-8ac2badf999f
-- title:
--   Global Theory: finite and ncard set Of index pi le
-- statement:
--   The Global Theory construction uses the finite and ncard set Of index pi le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L123-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {M : Type*} [AddCommGroup M]

theorem GlobalTheory.finite_and_ncard_setOf_index_pi_le (ρ : ℕ) {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.Finite ∧
      {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.ncard ≤ m ^ ρ := by sorry
