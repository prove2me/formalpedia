-- Prove2me | Theorems.Thm_OracleRO_DualSubgrad_theorem_3
-- name    : OracleRO.DualSubgrad.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:12:38.839678+00:00
-- url     : https://prove2.me/theorems/72856194-4818-4304-9289-e3380afdaaaa
-- title:
--   Theorem 3 — Algorithm 1 returns a $2\epsilon$-approximate robust solution or correctly reports infeasibility, after at most $\lceil G^2D^2/\epsilon^2\rceil$ oracle calls
-- statement:
--   Let $\mathcal D\subseteq\mathbb R^n$ and $\mathcal U\subseteq\mathbb R^d$ be convex sets, let $P$ be a Euclidean projection operator onto $\mathcal U$, and let $f_1,\dots,f_m:\mathbb R^n\times\mathbb R^d\to\mathbb R$ satisfy, for every $i$:
--
--   1. $f_i(\cdot,u)$ is convex on $\mathcal D$ for every $u\in\mathcal U$;
--   2. $f_i(x,\cdot)$ is concave on $\mathcal U$ for every $x\in\mathcal D$;
--   3. $f_i(x,\cdot)$ is differentiable at every $u\in\mathcal U$ (for $x\in\mathcal D$), with gradient $\nabla_u f_i(x,u)$ satisfying $\|\nabla_u f_i(x,u)\|_2\le G$.
--
--   Let $D\ge\|u-v\|_2$ for all $u,v\in\mathcal U$, let $\epsilon,D,G>0$, let $u^0_1,\dots,u^0_m\in\mathcal U$ and $x^0\in\mathcal D$, and let $\mathcal O_\epsilon$ be **any** $\epsilon$-approximate oracle as in Figure 1. Run Algorithm 1 with $T=\lceil G^2D^2/\epsilon^2\rceil$ and $\eta=D/(G\sqrt T)$. Then:
--
--   1. if it returns "infeasible", the robust problem (3) is infeasible: no $x\in\mathcal D$ satisfies $f_i(x,u)\le 0$ for all $i$ and all $u\in\mathcal U$;
--   2. if it returns a point $\bar x$, then $\bar x$ is a $2\epsilon$-approximate solution of (3):
--
--   $$
--   \bar x\in\mathcal D\qquad\text{and}\qquad f_i(\bar x,u)\le 2\epsilon\quad\text{for all } u\in\mathcal U,\ i=1,\dots,m;
--   $$
--
--   3. it calls the oracle at most $\lceil G^2D^2/\epsilon^2\rceil$ times.
--
--   The theorem reduces robust convex optimization with a concave-in-the-noise, convex uncertainty structure to a number of calls, independent of the dimension, to a solver of the original non-robust problem.
--
--   **Formalization Note** The paper writes $O(G^2D^2/\epsilon^2)$ calls; the algorithm makes at most one call per round and $T=\lceil G^2D^2/\epsilon^2\rceil$ rounds, so the explicit count is $\lceil G^2D^2/\epsilon^2\rceil$. Positivity of $D$ and $G$ is added (the step size divides by $G\sqrt T$, and $T\ge1$ needs $GD>0$), as is the initial point $x^0\in\mathcal D$ used by the first dual update, which the algorithm leaves undefined. Nonemptiness of $\mathcal U$ follows from the existence of the projection. The oracle is universally quantified, and "infeasible" is a conclusion about the robust problem, not the nominal one.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 7, Theorem 3 (proof pp. 7–8)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1

namespace OracleRO.DualSubgrad

/-- Theorem 3, p. 7: for every `ε`-approximate oracle (Figure 1), Algorithm 1 either returns a
`2ε`-approximate solution of the robust problem (3) or returns "infeasible", in which case (3) is
infeasible; and it makes at most `⌈G²D²/ε²⌉` oracle calls. -/
theorem theorem_3
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hDom : Convex ℝ Dom) (hU : Convex ℝ U) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconv : ∀ i, ∀ u ∈ U, ConvexOn ℝ Dom (fun x => f i x u))
    (hconc : ∀ i, ∀ x ∈ Dom, ConcaveOn ℝ U (f i x))
    (hgrad : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, HasGradientAt (f i x) (gradU i x u) u)
    (hgradG : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, ‖gradU i x u‖ ≤ G)
    (hdiam : ∀ u ∈ U, ∀ v ∈ U, ‖u - v‖ ≤ D)
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hu0 : ∀ i, u0 i ∈ U) (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) :
    (alg1Output gradU P O G D ε u0 x0 = none → ¬ RobustFeasible Dom U f) ∧
    (∀ xbar, alg1Output gradU P O G D ε u0 x0 = some xbar →
      IsApproxSolution Dom U f (2 * ε) xbar) ∧
    alg1Calls gradU P O G D ε u0 x0 ≤ ⌈G ^ 2 * D ^ 2 / ε ^ 2⌉₊ := by sorry

end OracleRO.DualSubgrad
