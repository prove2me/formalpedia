-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_rank_mul_idem
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_rank_mul_idem
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:51:48.64785+00:00
-- url     : https://prove2.me/theorems/66b44682-2e1d-42a4-80c3-e12a62d37be5
-- title:
--   Rank of conjugated Kronecker of idempotents
-- statement:
--   If $S Si=1=Si S$ and $A,B$ are idempotent, then $\operatorname{rank}(K(S,Si,A,B))=\operatorname{rank}(A)\cdot\operatorname{rank}(B)$.
-- source:
--   K_rank calculus

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem K_rank_mul_idem (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) (A B : M23)
    (hA : A * A = A) (hB : B * B = B) :
    (K S Si A B).rank = A.rank * B.rank := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
