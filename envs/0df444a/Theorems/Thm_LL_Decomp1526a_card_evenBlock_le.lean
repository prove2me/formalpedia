-- Prove2me | Theorems.Thm_LL_Decomp1526a_card_evenBlock_le
-- name    : LL_Decomp1526a.card_evenBlock_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:05:30.378598+00:00
-- url     : https://prove2.me/theorems/e053c0f1-961d-4767-a5ba-d4496ef7e15c
-- title:
--   Size of the even block
-- statement:
--   For every real $X\ge 0$, the number of even natural numbers $N$ with $\lfloor X\rfloor<N\le\lfloor 2X\rfloor$ is at most $X/2+1$, as a real number.
-- source:
--   Ramaré 1995, Section 2.3, p. 653, the expected count $X/2$.

import Mathlib
import Definitions.Def_LL_Decomp1526a_evenBlock

open Finset Real
open scoped Chebyshev Classical

namespace LL_Decomp1526a
theorem card_evenBlock_le {X : ℝ} (hX : 0 ≤ X) : (#(evenBlock X) : ℝ) ≤ X / 2 + 1 := by sorry
end LL_Decomp1526a
