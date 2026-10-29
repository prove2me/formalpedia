-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_IsPiv_diag_of_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.IsPiv_diag_of_rank
-- status  : Disproved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:54:16.016619+00:00
-- url     : https://prove2.me/theorems/6744ba70-f1a3-4bc1-a1b0-1ea615f844a4
-- title:
--   Flag-aligned rank-r matrix has first r diagonal pivots
-- statement:
--   # Diagonal Bruhat pivots from rank
--
--   If a $529\times 529$ rational matrix $q$ is flag-aligned of rank $r<529$, then
--   $$\forall\,k<r,\qquad \mathrm{IsPiv}(q,k,k).$$
--   Used for `net0O2_*_K_pivs`.
-- source:
--   K_pivs calculus

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit.NB
open Matrix

theorem IsPiv_diag_of_rank (q : Matrix (Fin 529) (Fin 529) ℚ) (r : ℕ)
    (hr : q.rank = r) (hrm : r < 529) :
    ∀ k, k < r → IsPiv q k k := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
