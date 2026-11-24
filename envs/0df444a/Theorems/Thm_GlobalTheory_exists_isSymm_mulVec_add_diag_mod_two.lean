-- Prove2me | Theorems.Thm_GlobalTheory_exists_isSymm_mulVec_add_diag_mod_two
-- name    : GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:16.503551+00:00
-- url     : https://prove2.me/theorems/372f0075-6e32-4e52-80eb-c6dc8eef8c99
-- title:
--   Global Theory: exists is Symm mul Vec add diag mod two
-- statement:
--   The Global Theory construction uses the exists is Symm mul Vec add diag mod two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsIsSymmMulVecAddDiagModTwo.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsIsSymmMulVecAddDiagModTwo.lean#L5-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsSymmMulVecAddDiagModTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two :
    ∀ (g : ℕ) (n n' : Fin g → ℤ), Even (n ⬝ᵥ n') →
      ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧
        ∀ i, (2 : ℤ) ∣ (S.mulVec n) i + S i i - n' i := by sorry
