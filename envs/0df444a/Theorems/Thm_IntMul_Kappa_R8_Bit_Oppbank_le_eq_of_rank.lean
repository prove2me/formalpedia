-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_le_eq_of_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.le_eq_of_rank
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:12:08.104924+00:00
-- url     : https://prove2.me/theorems/12e76057-8641-478a-8b75-120ee46f95a1
-- title:
--   Nested equal-rank idempotents are equal
-- statement:
--   If idempotents satisfy $\mathrm{Le}\,A\,B$ and $\mathrm{rank}\,B\le\mathrm{rank}\,A$, then $A=B$. Pure matrix fact (R6 `le_eq_of_rank`).
-- source:
--   R6 le_eq_of_rank

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2

theorem le_eq_of_rank {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ}
    (hA : A * A = A) (hB : B * B = B) (h : Le A B) (hr : B.rank ≤ A.rank) : B = A := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
