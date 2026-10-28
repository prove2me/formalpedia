-- Prove2me | Theorems.Thm_LL_Linnik1536a_four_pow_le
-- name    : LL_Linnik1536a.four_pow_le
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-27T21:46:08.524981+00:00
-- url     : https://prove2.me/theorems/f83aca82-d836-43a6-bc4b-0323f8cf44ad
-- title:
--   $4^j\le(2j+1)\binom{2j}{j}$
-- statement:
--   For every natural $j$, $4^j\le(2j+1)\binom{2j}{j}$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I, Acta Arith. 109 (2003), 169-194, Sections 4 and 7

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace LL_Linnik1536a

theorem four_pow_le (j : ℕ) : (4 : ℝ) ^ j ≤ (2 * j + 1) * Nat.centralBinom j := by sorry

end LL_Linnik1536a
