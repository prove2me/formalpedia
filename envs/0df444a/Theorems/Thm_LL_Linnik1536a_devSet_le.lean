-- Prove2me | Theorems.Thm_LL_Linnik1536a_devSet_le
-- name    : LL_Linnik1536a.devSet_le
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-27T21:48:21.091894+00:00
-- url     : https://prove2.me/theorems/e7fab6ff-613a-4fdd-99eb-b98abca57112
-- title:
--   Large deviation bound for $G_L$
-- statement:
--   For $\lambda\ge0$, the measure of $\{x\in[0,1]:|G_L(x)|>dL\}$ is at most $11(1+\lambda L)e^{-\lambda dL}E_L(\lambda)$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I, Acta Arith. 109 (2003), 169-194, Sections 4 and 7

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace LL_Linnik1536a

theorem devSet_le (L : ℕ) (d : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    volume (devSet L d) ≤
      ENNReal.ofReal (11 * (1 + lam * L) * Real.exp (-(lam * d * L)) * EL L lam) := by sorry

end LL_Linnik1536a
