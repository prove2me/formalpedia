-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_corollary_3_2
-- name    : FreedmanTail.Bernstein.corollary_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:50:36.110562+00:00
-- url     : https://prove2.me/theorems/8e002c37-e7d9-4dca-8130-67ad79d32ec4
-- title:
--   (3.2) Corollary — exp(λx) ≤ 1 + λx + x²e(λ) for λ ≥ 0 and x ≤ 1
-- statement:
--   Let $e(\lambda)=e^{\lambda}-1-\lambda$. For every $\lambda\ge0$ and every real $x\le1$,
--   $$\exp(\lambda x)\le 1+\lambda x+x^{2}e(\lambda).$$
--
--   This pointwise inequality converts an upper bound $X\le1$ on a random variable into a bound on its moment generating function in terms of its second moment; no lower bound on $x$ is needed.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 106 (PDF p. 7), (3.2) Corollary

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents

namespace FreedmanTail.Bernstein

/-- Freedman (1975), (3.2) Corollary, p. 106: `exp(λx) ≤ 1 + λx + x² e(λ)` for `λ ≥ 0`, `x ≤ 1`. -/
theorem corollary_3_2 (lam x : ℝ) (hlam : 0 ≤ lam) (hx : x ≤ 1) :
    Real.exp (lam * x) ≤ 1 + lam * x + x ^ 2 * e lam := by sorry

end FreedmanTail.Bernstein
