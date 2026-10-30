-- Prove2me | Theorems.Thm_OnlineConvexOpt_Approachability_theorem_3_1
-- name    : OnlineConvexOpt.Approachability.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:43:25.223499+00:00
-- url     : https://prove2.me/theorems/3dd779dc-21bc-4985-9faf-7ba147cd3112
-- title:
--   Theorem 3.1: online gradient descent has regret at most $\frac32 GD\sqrt T$
-- statement:
--   Let $\mathcal K\subseteq\mathbb R^d$ be closed and convex, with $\|x-z\|\le D$ for all $x,z\in\mathcal K$, and let $G>0$. Let $f_1,f_2,\dots$ be convex on $\mathcal K$. Run online gradient descent (Algorithm 8) from $x_1\in\mathcal K$ with step sizes $\eta_t=\dfrac{D}{G\sqrt t}$:
--
--   $$
--   x_{t+1}=\Pi_{\mathcal K}\bigl(x_t-\eta_t\nabla_t\bigr),
--   $$
--
--   where $\nabla_t$ is a subgradient of $f_t$ at $x_t$ relative to $\mathcal K$ (that is, $f_t(z)\ge f_t(x_t)+\nabla_t^\top(z-x_t)$ for all $z\in\mathcal K$) with $\|\nabla_t\|\le G$. Then for every $T\ge 1$ and every $x^\star\in\mathcal K$,
--
--   $$
--   \sum_{t=1}^T f_t(x_t)-\sum_{t=1}^T f_t(x^\star)\le\frac32\,GD\sqrt T .
--   $$
--
--   Equivalently $\mathrm{Regret}_T=\sum_{t=1}^T f_t(x_t)-\min_{x^\star\in\mathcal K}\sum_{t=1}^T f_t(x^\star)\le\frac32 GD\sqrt T$. This is the OCO guarantee that, plugged into the reduction of Theorem 13.7, gives Blackwell approachability at rate $O(1/\sqrt T)$.
--
--   **Formalization Note** Rounds are numbered from $0$ in Lean: round $t$ uses the step $D/(G\sqrt{t+1})$, the book's $\eta_{t+1}$, and the sum over $t<T$ is the book's $\sum_{t=1}^T$. $\Pi_{\mathcal K}$ is the predicate `IsProjection`.
--
--   Differences from the source:
--   - generalization: G > 0 bounds ‖∇f(x)‖ for all subgradients of f at all x ∈ K → G > 0 bounds the norms ‖g_t‖ of the subgradients used by the algorithm; reason: the book's G is such a bound, and the proof (3.3) uses only ‖∇_t‖ ≤ G
--   - encoding: min_{x⋆∈K} Σ f_t(x⋆) in the regret → the bound for every x⋆ ∈ K; reason: the same inequality; no attainment needed
--   - encoding: rounds t = 1, …, T with η_t = D/(G√t) → rounds t = 0, …, T − 1 with step D/(G√(t+1)); reason: index shift by one; the same run
--   - encoding: K bounded, convex and closed with diameter bound D → K convex and closed with ‖x − z‖ ≤ D on K; reason: boundedness follows from the diameter bound
--   - encoding: f_t : K → ℝ convex, a run of horizon T → f t : ℝ^d → ℝ convex on K, subgradients relative to K; infinite sequences and the bound for every T ≥ 1; reason: values outside K are not used; the step sizes do not depend on T, so a horizon-T run is the first T rounds of the infinite one
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Theorem 3.1, p. 43 (PDF p. 65); Algorithm 8, p. 42 (PDF p. 64); setting of §2.1, pp. 17–18 (PDF pp. 39–40)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_IsProjection

open scoped InnerProductSpace

namespace OnlineConvexOpt.Approachability

/-- **Theorem 3.1 (regret of online gradient descent).**
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Theorem 3.1,
p. 43: "Online gradient descent with step sizes {η_t = D/(G√t), t ∈ [T]} guarantees the following
for all T ≥ 1: Regret_T = Σ_{t=1}^T f_t(x_t) − min_{x⋆∈K} Σ_{t=1}^T f_t(x⋆) ≤ (3/2)GD√T."
Algorithm 8, p. 42: "y_{t+1} = x_t − η_t∇f_t(x_t), x_{t+1} = Π_K(y_{t+1})", from `x_1 ∈ K`.
Setting (§2.1, pp. 17–18): `K` bounded, convex and closed, `‖x − y‖ ≤ D` on `K`, `f_t` convex,
`∇f(x)` a subgradient relative to `K`, `G > 0` a bound on the subgradient norms.

Let `K ⊆ ℝ^d` be closed and convex with `‖x − z‖ ≤ D` for all `x, z ∈ K`, let `G > 0`, and let
`f_0, f_1, …` be convex on `K`. Let `x_0 ∈ K`, and for each round `t` let `g_t` be a subgradient
of `f_t` at `x_t` relative to `K` with `‖g_t‖ ≤ G`, and
`x_{t+1} = Π_K(x_t − D/(G√(t+1)) g_t)`. Then for every `T ≥ 1` and every `x⋆ ∈ K`,
`∑_{t<T} (f_t(x_t) − f_t(x⋆)) ≤ (3/2) G D √T`.

**Formalization Note.**
* Rounds are 0-indexed: Lean round `t` is the book's round `t + 1`, so its step size is the
  book's `η_{t+1} = D/(G√(t+1))`, and `∑_{t ∈ range T}` is the book's `Σ_{t=1}^T`.
* Reading R5: `min_{x⋆∈K}` is written "for every `x⋆ ∈ K`" (the same bound, with no attainment
  needed). `G` bounds the norms of the subgradients the algorithm uses, `‖g_t‖ ≤ G`, instead of
  all subgradients over `K` (the book's `G` is such a bound).
* Subgradients are relative to `K`, as defined on p. 18: `f(z) ≥ f(x) + ∇f(x)⊤(z − x)` for all
  `z ∈ K`. `Π_K` is the predicate `IsProjection`.
* Boundedness of `K` is implied by the diameter bound `D`. The step sizes do not depend on the
  horizon `T` (anytime), so the run is one infinite sequence and the bound holds for every
  `T ≥ 1`; the costs are an arbitrary fixed sequence, which covers adaptively chosen costs. -/
theorem theorem_3_1 {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K)
    (hK : IsClosed K) (D G : ℝ) (hG : 0 < G)
    (hD : ∀ x ∈ K, ∀ z ∈ K, ‖x - z‖ ≤ D)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ K (f t))
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (hx0 : x 0 ∈ K)
    (hsub : ∀ t, ∀ z ∈ K, f t (x t) + ⟪g t, z - x t⟫_ℝ ≤ f t z)
    (hgG : ∀ t, ‖g t‖ ≤ G)
    (hstep : ∀ t, IsProjection K (x t - (D / (G * Real.sqrt ((t : ℝ) + 1))) • g t) (x (t + 1))) :
    ∀ T : ℕ, 1 ≤ T → ∀ xs ∈ K,
      ∑ t ∈ Finset.range T, (f t (x t) - f t xs) ≤ 3 / 2 * G * D * Real.sqrt T := by sorry

end OnlineConvexOpt.Approachability
