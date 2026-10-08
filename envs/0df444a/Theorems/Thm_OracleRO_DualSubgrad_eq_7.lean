-- Prove2me | Theorems.Thm_OracleRO_DualSubgrad_eq_7
-- name    : OracleRO.DualSubgrad.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T09:11:51.17083+00:00
-- url     : https://prove2.me/theorems/ff490850-2463-46e6-b07f-5779b354ae70
-- title:
--   Eq. (7) — the dual iterates of Algorithm 1 have average regret at most $GD/\sqrt T\le\epsilon$
-- statement:
--   Assume the setting of §3.1: $\mathcal U\subseteq\mathbb R^d$ is convex with Euclidean projection operator $P$ and $\|u-v\|_2\le D$ for $u,v\in\mathcal U$; for every $i$ and every $x\in\mathcal D$ the function $f_i(x,\cdot)$ is concave on $\mathcal U$ and differentiable at every $u\in\mathcal U$ with $\|\nabla_u f_i(x,u)\|_2\le G$; $\epsilon,D,G>0$; $u^0_i\in\mathcal U$ for all $i$ and $x^0\in\mathcal D$; and $\mathcal O_\epsilon$ is an $\epsilon$-approximate oracle (Figure 1). Let $(u^t,x^t)$ be the iterates of Algorithm 1 with $T=\lceil G^2D^2/\epsilon^2\rceil$. Then for every $i\in[m]$ and every $u\in\mathcal U$,
--
--   $$
--   \frac1T\sum_{t=1}^T f_i(x^t,u)-\frac1T\sum_{t=1}^T f_i(x^t,u^t_i)\le\frac{GD}{\sqrt T}\le\epsilon .
--   $$
--
--   This is the dual half of the proof of Theorem 3: for each constraint, the dual update is online gradient ascent on the rewards $f_i(x^t,\cdot)$, whose regret guarantee (Lemma 1) holds even though $x^t$ is chosen after $u^t$.
--
--   **Formalization Note** The page writes $\max_{u_i\in\mathcal U}$; the statement is for every $u\in\mathcal U$, which is equivalent without assuming attainment. The bound holds for the defined iterates whatever the oracle answers (rounds after an "infeasible" answer use $x^t=x^0\in\mathcal D$).
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 8, proof of Theorem 3, (7)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1

namespace OracleRO.DualSubgrad

/-- Eq. (7), p. 8: in the run of Algorithm 1, for every constraint `i` and every `u ∈ 𝒰`,
`(1/T) ∑_{t=1}^T f_i(x^t, u) - (1/T) ∑_{t=1}^T f_i(x^t, u^t_i) ≤ G D / √T ≤ ε`
(the regret guarantee of online gradient ascent on the rewards `f_i(x^t, ·)`). -/
theorem eq_7
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hU : Convex ℝ U) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconc : ∀ i, ∀ x ∈ Dom, ConcaveOn ℝ U (f i x))
    (hgrad : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, HasGradientAt (f i x) (gradU i x u) u)
    (hgradG : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, ‖gradU i x u‖ ≤ G)
    (hdiam : ∀ u ∈ U, ∀ v ∈ U, ‖u - v‖ ≤ D)
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hu0 : ∀ i, u0 i ∈ U) (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) :
    ∀ i, ∀ u ∈ U,
      (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
          f i (alg1X gradU P O G D ε u0 x0 t) u
        - (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
          f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i)
        ≤ G * D / Real.sqrt (alg1T G D ε) ∧
      G * D / Real.sqrt (alg1T G D ε) ≤ ε := by sorry

end OracleRO.DualSubgrad
