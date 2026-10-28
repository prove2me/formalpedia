-- Prove2me | Theorems.Thm_LL_Linnik1536a_even_partial_le_int_exp
-- name    : LL_Linnik1536a.even_partial_le_int_exp
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-27T21:47:16.107954+00:00
-- url     : https://prove2.me/theorems/e0a774e7-d153-4475-9125-6a9164651f2e
-- title:
--   Even partial exponential moments
-- statement:
--   If $f$ is continuous on $\mathbb R$ with all moments $\int_0^1 f^n\ge0$ and $\lambda\ge0$, then $\sum_{j<K}\frac{\lambda^{2j}}{(2j)!}\int_0^1 f^{2j}\le\int_0^1 e^{\lambda f}$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I, Acta Arith. 109 (2003), 169-194, Sections 4 and 7

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace LL_Linnik1536a

theorem even_partial_le_int_exp {f : ℝ → ℝ} (hf : Continuous f)
    (hmom : ∀ n : ℕ, 0 ≤ ∫ x in (0 : ℝ)..1, f x ^ n) {lam : ℝ} (hlam : 0 ≤ lam) (K : ℕ) :
    ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ∫ x in (0 : ℝ)..1, f x ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, Real.exp (lam * f x) := by sorry

end LL_Linnik1536a
