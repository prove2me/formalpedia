-- Prove2me | Theorems.Thm_Freiman_localValue_constant
-- name    : Freiman.localValue_constant
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:45.915396+00:00
-- url     : https://prove2.me/theorems/abf0c80a-8720-4d2f-93d5-87ed311eb76c
-- title:
--   localValue constant
-- statement:
--   The constant digit word has every local value equal to $\sqrt{d^2+4}$. This is the background value used for windows crossing padded joins.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic

open Freiman

theorem Freiman.localValue_constant (d : ℕ+) (i : ℤ) :
    localValue (fun _ : ℤ => d) i = Real.sqrt ((((d : ℕ) : ℝ) ^ 2) + 4) := by sorry
