-- Prove2me | Theorems.Thm_LL_Linnik1536a_lemma4_GL
-- name    : LL_Linnik1536a.lemma4_GL
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-27T21:47:55.613216+00:00
-- url     : https://prove2.me/theorems/bddabd3c-4f5f-476d-85ce-5fc7078d2099
-- title:
--   Lemma 4 for $G_L$, weak constant
-- statement:
--   For $\lambda\ge0$, $\int_0^1 e^{\lambda|G_L|}\le 11(1+\lambda L)E_L(\lambda)$, a weak form of Lemma 4 of Pintz and Ruzsa.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I, Acta Arith. 109 (2003), 169-194, Sections 4 and 7

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace LL_Linnik1536a

theorem lemma4_GL (L : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖Gpow L x‖) ≤ 11 * (1 + lam * L) * EL L lam := by sorry

end LL_Linnik1536a
