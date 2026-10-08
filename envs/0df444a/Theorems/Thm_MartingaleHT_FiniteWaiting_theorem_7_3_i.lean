-- Prove2me | Theorems.Thm_MartingaleHT_FiniteWaiting_theorem_7_3_i
-- name    : MartingaleHT.FiniteWaiting.theorem_7_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:52.055219+00:00
-- url     : https://prove2.me/theorems/cf699cfe-19c1-499a-866c-02d81f298a5c
-- title:
--   Theorem 7.3 (i) — the integral representation with reflection at $\kappa$ is well posed and continuous for u.o.c. convergence
-- statement:
--   Let $\kappa\in\mathbb R$ and let $h:\mathbb R\to\mathbb R$ satisfy $h(0)=0$ and be Lipschitz: there is $c>0$ with $|h(s_1)-h(s_2)|\le c|s_1-s_2|$ for all $s_1,s_2$. Consider the integral representation with reflection at the upper barrier $\kappa$:
--   $$
--   x(t)=b+y(t)+\int_0^t h(x(s))\,ds-u(t),\qquad t\ge0,
--   $$
--   with $x\le\kappa$, $u$ nondecreasing and nonnegative in $D$, and $\int_0^\infty \mathbf 1\{x(t)<\kappa\}\,du(t)=0$. Then:
--
--   1. for every $y\in D$ and $b\in\mathbb R$ there is a solution $(x,u)$, and any two solutions agree on $[0,\infty)$;
--   2. the solution map $(y,b)\mapsto(x,u)$ is continuous when $D$ carries the topology of uniform convergence on bounded intervals: if $b_k\to b$ and $\sup_{0\le t\le T}|y_k(t)-y(t)|\to0$ for every $T\ge0$, then $\sup_{0\le t\le T}|x_k(t)-x(t)|\to0$ and $\sup_{0\le t\le T}|u_k(t)-u(t)|\to0$ for every $T\ge0$;
--   3. if $y$ is continuous on $[0,\infty)$, so are $x$ and $u$.
--
--   The theorem turns the martingale representation of the $M/M/n/m_n+M$ queue into a continuous function of its driving noise, which is what lets the continuous-mapping theorem carry the noise's limit to the queue's limit.
--
--   **Formalization Note** Part (ii) of the paper's Theorem 7.3, continuity for the Skorohod $J_1$ topology, is not part of this statement. Continuity is stated in sequential form, which is equivalent for the topology of uniform convergence on bounded intervals (it is metrizable); the uniform distance on $[0,T]$ is `BellWilliams2001.ThresholdPolicy.supDist` on $\mathbb R^1$, valued in $[0,\infty]$. Uniqueness is on $[0,\infty)$ only, because paths are functions on $\mathbb R$ whose negative-time values are ignored.
-- source:
--   Pang, Talreja & Whitt, Martingale Proofs of Many-Server Heavy-Traffic Limits for Markovian Queues, arXiv:0712.4211v1 (reprint of Probab. Surveys 4 (2007) 193–267), p. 250, Theorem 7.3 (existence, uniqueness, part (i), continuity clause); p. 225, (62)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_MartingaleHT_FiniteWaiting_Reflection

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MartingaleHT.FiniteWaiting

open BellWilliams2001.ThresholdPolicy

/-- **Theorem 7.3**, existence, uniqueness, continuity (i) and the continuity clause (p. 250).
Let `κ ∈ ℝ` and let `h : ℝ → ℝ` satisfy `h(0) = 0` and be Lipschitz as in (62). Then:
1. for every `y ∈ D` and `b ∈ ℝ` the reflected integral representation (111) has a solution
   `(x, u)`, unique on `[0, ∞)`;
2. the solution map `(y, b) ↦ (x, u)` is continuous for uniform convergence on bounded
   intervals (in sequential form: `bₖ → b` and `yₖ → y` uniformly on every `[0, T]` imply
   `xₖ → x` and `uₖ → u` uniformly on every `[0, T]`);
3. if `y` is continuous on `[0, ∞)`, so are `x` and `u`. -/
theorem theorem_7_3_i (κ : ℝ) (h : ℝ → ℝ) (h0 : h 0 = 0)
    (hLip : ∃ c : ℝ, 0 < c ∧ ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|) :
    (∀ (y : ℝ → ℝ) (b : ℝ), IsCadlag y →
      ∃ x u : ℝ → ℝ, IsReflectedIntegralSolution κ h b y x u ∧
        ∀ x' u' : ℝ → ℝ, IsReflectedIntegralSolution κ h b y x' u' →
          ∀ t : ℝ, 0 ≤ t → x' t = x t ∧ u' t = u t) ∧
    (∀ (y : ℕ → ℝ → ℝ) (b : ℕ → ℝ) (x u : ℕ → ℝ → ℝ) (y₀ : ℝ → ℝ) (b₀ : ℝ)
        (x₀ u₀ : ℝ → ℝ),
      (∀ k, IsCadlag (y k)) → IsCadlag y₀ →
      (∀ k, IsReflectedIntegralSolution κ h (b k) (y k) (x k) (u k)) →
      IsReflectedIntegralSolution κ h b₀ y₀ x₀ u₀ →
      Tendsto b atTop (𝓝 b₀) →
      (∀ T : ℝ, 0 ≤ T → Tendsto (fun k => supDist (fun t (_ : Fin 1) => y k t)
        (fun t (_ : Fin 1) => y₀ t) T) atTop (𝓝 0)) →
      ∀ T : ℝ, 0 ≤ T →
        Tendsto (fun k => supDist (fun t (_ : Fin 1) => x k t)
          (fun t (_ : Fin 1) => x₀ t) T) atTop (𝓝 0) ∧
        Tendsto (fun k => supDist (fun t (_ : Fin 1) => u k t)
          (fun t (_ : Fin 1) => u₀ t) T) atTop (𝓝 0)) ∧
    (∀ (y : ℝ → ℝ) (b : ℝ) (x u : ℝ → ℝ), ContinuousOn y (Set.Ici 0) →
      IsReflectedIntegralSolution κ h b y x u →
      ContinuousOn x (Set.Ici 0) ∧ ContinuousOn u (Set.Ici 0)) := by sorry

end MartingaleHT.FiniteWaiting
