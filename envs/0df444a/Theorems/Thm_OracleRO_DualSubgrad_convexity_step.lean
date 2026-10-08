-- Prove2me | Theorems.Thm_OracleRO_DualSubgrad_convexity_step
-- name    : OracleRO.DualSubgrad.convexity_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:12:16.31499+00:00
-- url     : https://prove2.me/theorems/19148e68-1372-4d0a-9958-43b932985c97
-- title:
--   Proof of Theorem 3, final inequality — $f_i(\bar x,u)\le\frac1T\sum_t f_i(x^t,u)$ by convexity in $x$
-- statement:
--   Let $\mathcal D\subseteq\mathbb R^n$ be convex, let $f_i(\cdot,u)$ be convex on $\mathcal D$ for every $i$ and every $u\in\mathcal U$, let $P$ be a Euclidean projection operator onto $\mathcal U$, let $\epsilon,D,G>0$, $x^0\in\mathcal D$, and let $\mathcal O_\epsilon$ be an $\epsilon$-approximate oracle (Figure 1). If Algorithm 1 returns $\bar x=\frac1T\sum_{t=1}^T x^t$, then for every $i\in[m]$ and every $u\in\mathcal U$,
--
--   $$
--   f_i(\bar x,u)\le\frac1T\sum_{t=1}^T f_i(x^t,u).
--   $$
--
--   This is the last inequality of the chain on p. 8, which the page justifies "from the convexity of the functions $f_i$ with respect to $x$"; together with (6) and (7) it gives $f_i(\bar x,u)\le 2\epsilon$.
--
--   **Formalization Note** The page's chain reads "Combining (10) and (12)"; the references are to (6) and (7). Of the chain, this item states only its final inequality, in the $\forall u\in\mathcal U$ form (the page writes $\max_{u_i\in\mathcal U}$ on both sides); the other two inequalities are (6) and (7).
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 8, §3.1, proof of Theorem 3, display after (7)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1

namespace OracleRO.DualSubgrad

/-- Proof of Theorem 3, display after (7), p. 8 (its final inequality): if Algorithm 1 returns
`x̄ = (1/T) ∑_{t=1}^T x^t`, then by convexity of `f_i(·, u)` on `𝒟`,
`f_i(x̄, u) ≤ (1/T) ∑_{t=1}^T f_i(x^t, u)` for every constraint `i` and every `u ∈ 𝒰`. -/
theorem convexity_step
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hDom : Convex ℝ Dom) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconv : ∀ i, ∀ u ∈ U, ConvexOn ℝ Dom (fun x => f i x u))
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O)
    (xbar : EuclideanSpace ℝ (Fin n))
    (hout : alg1Output gradU P O G D ε u0 x0 = some xbar) :
    ∀ i, ∀ u ∈ U, f i xbar u ≤ (1 / (alg1T G D ε : ℝ)) *
      ∑ t ∈ Finset.Icc 1 (alg1T G D ε), f i (alg1X gradU P O G D ε u0 x0 t) u := by sorry

end OracleRO.DualSubgrad
