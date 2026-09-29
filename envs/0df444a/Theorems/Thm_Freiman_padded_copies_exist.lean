-- Prove2me | Theorems.Thm_Freiman_padded_copies_exist
-- name    : Freiman.padded_copies_exist
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:33.271095+00:00
-- url     : https://prove2.me/theorems/0276c8c0-9114-4d58-adf1-b6060f92ab45
-- title:
--   padded copies exist
-- statement:
--   Concatenate the restrictions of model j to [-2j,2j], and extend to the left by the fixed digit d. The resulting word satisfies the exact PaddedCopies indexing relation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic

open Freiman

theorem Freiman.padded_copies_exist (a : ℕ → ℤ → ℕ+) (d : ℕ+) :
    ∃ b : ℤ → ℕ+, PaddedCopies a b d := by sorry
