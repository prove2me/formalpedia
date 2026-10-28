-- Prove2me | Theorems.Thm_LL_Linnik1536a_moment_binom
-- name    : LL_Linnik1536a.moment_binom
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-27T21:45:34.90893+00:00
-- url     : https://prove2.me/theorems/99dae314-4aa5-43d7-972b-a29d637f10ce
-- title:
--   Moments of $|G_L|$ against moments of $S_L$
-- statement:
--   $\binom{2j}{j}4^{-j}\int_0^1|G_L|^{2j}\le\int_0^1 S_L^{2j}$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I, Acta Arith. 109 (2003), 169-194, Sections 4 and 7

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace LL_Linnik1536a

theorem moment_binom (L j : ℕ) :
    (Nat.centralBinom j : ℝ) / 4 ^ j * ∫ x in (0 : ℝ)..1, ‖Gpow L x‖ ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, Spow L x ^ (2 * j) := by sorry

end LL_Linnik1536a
