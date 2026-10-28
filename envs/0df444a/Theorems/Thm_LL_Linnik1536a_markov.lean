-- Prove2me | Theorems.Thm_LL_Linnik1536a_markov
-- name    : LL_Linnik1536a.markov
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-27T21:44:18.200393+00:00
-- url     : https://prove2.me/theorems/af70bad1-6531-468f-a760-34d4e6d5453c
-- title:
--   Exponential Chebyshev bound for large deviations of $G_L$
-- statement:
--   For $\lambda\ge0$, the Lebesgue measure of $\{x\in[0,1]:|G_L(x)|>dL\}$ is at most $e^{-\lambda dL}\int_0^1 e^{\lambda|G_L(x)|}dx$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I, Acta Arith. 109 (2003), 169-194, Sections 4 and 7

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace LL_Linnik1536a

theorem markov {L : ℕ} {d lam : ℝ} (hlam : 0 ≤ lam) :
    volume (devSet L d) ≤
      ENNReal.ofReal (Real.exp (-(lam * d * L)) * ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖)) := by sorry

end LL_Linnik1536a
