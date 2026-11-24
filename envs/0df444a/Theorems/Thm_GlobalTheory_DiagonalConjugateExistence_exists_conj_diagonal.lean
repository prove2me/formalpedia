-- Prove2me | Theorems.Thm_GlobalTheory_DiagonalConjugateExistence_exists_conj_diagonal
-- name    : GlobalTheory.DiagonalConjugateExistence.exists_conj_diagonal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:13:28.43082+00:00
-- url     : https://prove2.me/theorems/df04439a-90ba-4fe5-88ae-a92bcd0fd6be
-- title:
--   Diagonal Conjugate Existence: exists conj diagonal
-- statement:
--   The Diagonal Conjugate Existence construction uses the exists conj diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConjDiagonal.lean#L5-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsConjDiagonal.lean#L5-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsConjDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiagonalConjugateExistence

theorem GlobalTheory.DiagonalConjugateExistence.exists_conj_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ)
    (ht : Function.Injective t)
    (hA : Matrix.charpoly A = ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))) :
    ∃ P : GL (Fin n) ℂ, A * (P : Matrix (Fin n) (Fin n) ℂ)
      = (P : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal t := by sorry
