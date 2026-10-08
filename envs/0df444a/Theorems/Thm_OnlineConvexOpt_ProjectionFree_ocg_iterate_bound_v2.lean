-- Prove2me | Theorems.Thm_OnlineConvexOpt_ProjectionFree_ocg_iterate_bound_v2
-- name    : OnlineConvexOpt.ProjectionFree.ocg_iterate_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:22:25.169032+00:00
-- url     : https://prove2.me/theorems/013522f5-b53e-40bc-94eb-077709843352
-- title:
--   Lemma 7.4 — Online conditional gradient iterate bound $h_t\le2D^2\sigma_t$ for $1\le t\le T$
-- statement:
--   **Statement (Lemma 7.4).** Let $K$ be a nonempty convex set of diameter at most $D$, $f_1,f_2,\dots$ costs that are $G$-Lipschitz on $K$ with gradients $\nabla_t=\nabla f_t(x_t)$ of norm at most $G$ at the played points, and let $(x,v)$ be a run of Algorithm 27 for the horizon $T$ with $\eta=D/(2GT^{3/4})$ and $\sigma_t=\min\{1,2/\sqrt t\}$. With $F_t(x)=\eta\sum_{\tau<t}\nabla_\tau^\top x+\|x-x_1\|^2$ and $x^\star_t=\arg\min_{x\in K}F_t(x)$, the iterates satisfy, for every round $1\le t\le T$ of the run,
--   $$h_t=F_t(x_t)-F_t(x^\star_t)\le 2D^2\sigma_t .$$
--
--   **Formalization Note.** The retired statement quantified $t$ over all of $\mathbb N$ although $\eta$ is pinned by the fixed horizon $T$ and the algorithm runs only for $t\in[T]$; for rounds $t\gg T$ one late gradient moves the minimizer of $F_t$ by $\Theta(\eta G)$, which does not shrink with $t$, while $2D^2\sigma_t\sim4D^2/\sqrt t$ does (refuted at $t=4225$ with $T=1$). The round is now restricted to $t\le T$, the only range the book's "for all $t\ge1$" can refer to. The gradient-norm bound $\|\nabla_t\|\le G$ (the book's $G$, used in the Cauchy–Schwarz step of the proof) is restored alongside the Lipschitz condition. $x^\star_t$ is any minimizer of $F_t$ over $K$ (it is unique, $F_t$ being strictly convex); rounds are $1$-indexed.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 133, Lemma 7.4 (PDF p. 155)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

namespace OnlineConvexOpt.ProjectionFree

/-- Lemma 7.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 133, PDF p. 155). The iterates `x_t` of Algorithm 27 (run for the
horizon `T`, with the parameters `η = D/(2GT^{3/4})`, `σ_t = min{1, 2/√t}` of Theorem 7.3)
satisfy, for all rounds `1 ≤ t ≤ T` of the run, `h_t ≤ 2D²σ_t`, where
`h_t = F_t(x_t) - F_t(x⋆_t)` and `x⋆_t = arg min_{x∈K} F_t(x)`.

The book proves this lemma "as a first step in analyzing Algorithm 27" (§7.5), for the specific
parameters that Theorem 7.3 uses (the induction step's derivation, Eq. (7.6), explicitly
invokes these values and the bound `‖∇_t‖ ≤ G` on the cost gradients — the book's `G` bounds the
(sub)gradient norms over `K`, p. 20, which implies the `G`-Lipschitz condition also kept here).

Corrected version: the retired statement quantified `t` over all of `ℕ`, although `η` is pinned
by the fixed horizon `T` and Algorithm 27 runs only for `t ∈ [T]`; for rounds `t ≫ T` a single
gradient moves the minimizer of `F_t` by `Θ(ηG)`, which does not shrink with `t`, so the bound
`2D²σ_t ~ 4D²/√t` fails there. The round is now restricted to `t ≤ T`, the only range the book's
"for all `t ≥ 1`" can refer to. -/
theorem ocg_iterate_bound_v2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (gradf : ℕ → E) (hgradG : ∀ t : ℕ, 1 ≤ t → ‖gradf t‖ ≤ G)
    (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v)
    (xstar : ℕ → E)
    (hxstar : ∀ t : ℕ, 1 ≤ t → xstar t ∈ K ∧
      ∀ y ∈ K, AggregateFunction gradf x1 η t (xstar t) ≤ AggregateFunction gradf x1 η t y)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) :
    AggregateFunction gradf x1 η t (x t) - AggregateFunction gradf x1 η t (xstar t) ≤
      2 * D ^ 2 * σ t := by sorry

end OnlineConvexOpt.ProjectionFree
