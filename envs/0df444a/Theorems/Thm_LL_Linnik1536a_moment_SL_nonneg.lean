-- Prove2me | Theorems.Thm_LL_Linnik1536a_moment_SL_nonneg
-- name    : LL_Linnik1536a.moment_SL_nonneg
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-27T21:46:42.299027+00:00
-- url     : https://prove2.me/theorems/bb1c3ab3-5cf6-48ff-b3be-8c3daecd710d
-- title:
--   Nonnegative moments of $S_L$
-- statement:
--   Every moment $\int_0^1 S_L(x)^n dx$ is nonnegative.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I, Acta Arith. 109 (2003), 169-194, Sections 4 and 7

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace LL_Linnik1536a

theorem moment_SL_nonneg (L n : ℕ) : 0 ≤ ∫ x in (0 : ℝ)..1, Spow L x ^ n := by sorry

end LL_Linnik1536a
