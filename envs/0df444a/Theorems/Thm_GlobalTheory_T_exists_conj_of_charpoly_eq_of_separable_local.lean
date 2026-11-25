-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_conj_of_charpoly_eq_of_separable_local
-- name    : GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:00.557341+00:00
-- url     : https://prove2.me/theorems/c69705b5-bcef-4ceb-a66a-bb01bcefd06c
-- title:
--   T: exists conj of charpoly eq of separable local
-- statement:
--   The T construction uses the exists conj of charpoly eq of separable local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyLocalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyLocalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyLocalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R), Y.charpoly = Y'.charpoly → Y.charpoly.Separable → ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by sorry
