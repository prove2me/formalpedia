-- Prove2me | Theorems.Thm_GlobalTheory_exists_ker_eq_of_index_prime
-- name    : GlobalTheory.exists_ker_eq_of_index_prime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:17.225516+00:00
-- url     : https://prove2.me/theorems/03a3f37b-6c2a-4270-9800-3ccfe438bbc2
-- title:
--   Global Theory: exists ker eq of index prime
-- statement:
--   The Global Theory construction uses the exists ker eq of index prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L11-L17

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

theorem GlobalTheory.exists_ker_eq_of_index_prime {p : ℕ} (hp : p.Prime) (H : AddSubgroup M)
    (hH : H.index = p) : ∃ f : M →ₗ[ℤ] ZMod p, f.toAddMonoidHom.ker = H := by sorry
