-- Prove2me | Theorems.Thm_OnlineConvexOpt_ProjectionFree_ocg_regret_v2
-- name    : OnlineConvexOpt.ProjectionFree.ocg_regret_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:40:57.395971+00:00
-- url     : https://prove2.me/theorems/3e3c86ac-c73c-4569-bfc4-b074dc7fab2d
-- title:
--   Theorem 7.3 — Online conditional gradient regret $8DGT^{3/4}$ (genuine comparator over $K$)
-- statement:
--   **Statement (Theorem 7.3).** Let $K$ be a nonempty convex set of diameter at most $D$ in a real Hilbert space and $f_1,f_2,\dots$ cost functions convex on $K$, $G$-Lipschitz on $K$, whose gradients $\nabla_t=\nabla f_t(x_t)$ at the played points have norm at most $G$ (the book's $G$, p. 20). Run online conditional gradient (Algorithm 27) with $\eta=D/(2GT^{3/4})$ and $\sigma_t=\min\{1,2/\sqrt t\}$ from $x_1\in K$. Then for every $T\ge1$,
--   $$\mathrm{Regret}_T=\sum_{t=1}^{T}f_t(x_t)-\min_{x^\star\in K}\sum_{t=1}^{T}f_t(x^\star)\le 8DG\,T^{3/4}.$$
--
--   **Formalization Note.** The retired statement wrote the comparator as `⨅ xstar ∈ K, …`, which on $\mathbb R$ evaluates to the junk value $0$ outside $K$, so the subtracted term was $\le0$ for every bounded $K$ (refuted by constant costs). The comparator is now the real infimum of the image of $K$ under the cumulative cost, a genuine infimum since $K$ is nonempty and the Lipschitz costs are bounded on the bounded set $K$. The gradient-norm bound $\|\nabla_t\|\le G$ at the played points — the book's definition of $G$ — is restored alongside the two-point Lipschitz condition (the retired version kept only the latter). Everything else (parameters, run predicate, $1$-indexed rounds) is unchanged.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 133, Theorem 7.3 (PDF p. 155)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

namespace OnlineConvexOpt.ProjectionFree

/-- Theorem 7.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 133, PDF p. 155). Online conditional gradient (Algorithm 27) with
parameters `η = D/(2GT^{3/4})`, `σ_t = min{1, 2/√t}` attains
`Regret_T = Σ_{t=1}^T f_t(x_t) - min_{x⋆∈K} Σ_{t=1}^T f_t(x⋆) ≤ 8DGT^{3/4}`.

`K` (convex, nonempty, diameter `≤ D`) and the costs `f`, convex on `K`, `G`-Lipschitz on `K`
and with gradients of norm `≤ G` at the played points (the book's `G` bounds the (sub)gradient
norms over `K`, p. 20, which implies `G`-Lipschitzness), are the chapter-wide standing
hypotheses of §7.5, stated here as explicit hypotheses. `min_{x⋆∈K}` is the genuine infimum of
the cumulative cost over `K` (the book's `min`, since `K` is nonempty and the Lipschitz costs
are bounded on the bounded set `K`).

Corrected version: the retired statement wrote the comparator as the bounded binder
`⨅ xstar ∈ K, …`, which on `ℝ` evaluates to the junk value `sInf ∅ = 0` at every point outside
`K`, so the subtracted term was `≤ 0` for every bounded `K`; the gradient-norm bound of the
book's `G` was also restored alongside the Lipschitz condition. -/
theorem ocg_regret_v2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (gradf : ℕ → E) (hgradG : ∀ t : ℕ, 1 ≤ t → ‖gradf t‖ ≤ G)
    (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v) :
    (∑ t ∈ Finset.Icc 1 T, f t (x t)) -
        sInf ((fun xstar => ∑ t ∈ Finset.Icc 1 T, f t xstar) '' K) ≤
      8 * D * G * (T : ℝ) ^ (3 / 4 : ℝ) := by sorry

end OnlineConvexOpt.ProjectionFree
