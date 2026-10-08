-- Prove2me | Theorems.Thm_OracleRO_DualSubgrad_eq_6
-- name    : OracleRO.DualSubgrad.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:11:29.489821+00:00
-- url     : https://prove2.me/theorems/b67106a2-b73b-4973-9cdf-d71a1e6c29fa
-- title:
--   Eq. (6) — if Algorithm 1 returns $\bar x$, then $\frac1T\sum_t f_i(x^t,u^t_i)\le\epsilon$ for every $i$
-- statement:
--   Let $\mathcal O_\epsilon$ be an $\epsilon$-approximate oracle (Figure 1) for the domain $\mathcal D$, uncertainty set $\mathcal U$ and constraints $f_1,\dots,f_m$, let $P$ be a Euclidean projection operator onto $\mathcal U$, and let $\epsilon,D,G>0$. Consider the run of Algorithm 1 with $T=\lceil G^2D^2/\epsilon^2\rceil$ rounds and iterates $(u^t,x^t)$. If the algorithm returns a point $\bar x$ (that is, the oracle never declared infeasibility), then
--
--   $$
--   \forall i\in[m],\qquad \frac1T\sum_{t=1}^T f_i(x^t,u^t_i)\le\epsilon .
--   $$
--
--   This is the primal half of the proof of Theorem 3: each oracle answer meets its own nominal constraints up to $\epsilon$.
--
--   **Formalization Note** The iterates are those of the defined run `alg1State`; the dual points $u^t_i$ ($t\ge 1$) lie in $\mathcal U$ because they are projections, so the oracle's specification applies to every round.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 7, proof of Theorem 3, (6)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1

namespace OracleRO.DualSubgrad

/-- Eq. (6), p. 7: if Algorithm 1 returns a point, then for every constraint `i` the average of
`f_i(x^t, u^t_i)` over the rounds `t = 1, …, T` is at most `ε`. -/
theorem eq_6
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P) (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hO : IsApproxOracle Dom U f ε O)
    (xbar : EuclideanSpace ℝ (Fin n))
    (hout : alg1Output gradU P O G D ε u0 x0 = some xbar) :
    ∀ i, (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i) ≤ ε := by sorry

end OracleRO.DualSubgrad
