-- Prove2me | Theorems.Thm_OptimisticPSRL_Concentration_proof_prop5_2_predictable_variance
-- name    : OptimisticPSRL.Concentration.proof_prop5_2_predictable_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:39.660078+00:00
-- url     : https://prove2.me/theorems/3cfcad51-77a8-4dff-b268-fb43adae3671
-- title:
--   Proof of Proposition 5.2, p. 21 — Σₜ E[Zₜ²] = Σᵢ cᵢ² n γᵢ
-- statement:
--   Let $p\in\Delta^S$, $h\in\mathbb R^S$, $n\in\mathbb N$, and let $X$ be one multinoulli trial with parameter $p$. With $Z=\sum_iZ_i(X)$,
--
--   $$
--   \sum_{t=1}^n\mathbb E\big[Z^2\big]=\sum_ic_i^2\,n\,\gamma_i .
--   $$
--
--   Equivalently, the variance of $h(X)$ under $p$ equals $\sum_i\gamma_ic_i^2$. This identifies the predictable quadratic variation $V_n$ that enters Bernstein's inequality in the proof of Proposition 5.2, and so the variance term of its bound.
--
--   **Formalization Note** iid reading: the conditional expectation given $(s_{t-1},a_{t-1})$ is the expectation under one draw of law $p$ (the integral against `cat p`), the same for every $t$, and $\tau=n$. The sum over $i$ runs over all states; the last term vanishes because $\gamma_S=0$. The page's middle expression $\sum_t\sum_ic_i^2\mathbb E[Z_{t,i}^2|\cdot]$ counts the factor $c_i$ twice ($Z_{t,i}$ already contains it); only the outer equality, which is correct, is stated.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 21, proof of Proposition 5.2, display after "Therefore,"

import Mathlib
import Definitions.Def_OptimisticPSRL_Concentration_Setting

namespace OptimisticPSRL.Concentration

open MeasureTheory

/-- Proof of Proposition 5.2 (Agrawal–Jia, arXiv:1705.07041v3, p. 21, the "Therefore," display),
iid reading with `τ = n`: `∑_{t=1}^n E[Z_t²] = ∑_i c_i² n γ_i`, where `Z_t = ∑_i Z_{t,i}` is
evaluated at one trial with law `p`. -/
theorem proof_prop5_2_predictable_variance {S : ℕ} (n : ℕ) (p h : Fin S → ℝ)
    (hp : IsProbVec p) :
    ∑ _t : Fin n, ∫ x, (∑ i, Zcoord p h i x) ^ 2 ∂(cat p) =
      ∑ i, cCoef p h i ^ 2 * n * gammaCoef p i := by sorry

end OptimisticPSRL.Concentration
