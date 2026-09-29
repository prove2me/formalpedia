-- Prove2me | Theorems.Thm_OnlineConvexOpt_ProjectionFree_ocg_regret
-- name    : OnlineConvexOpt.ProjectionFree.ocg_regret
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:45:00.67766+00:00
-- url     : https://prove2.me/theorems/3c5c767c-6bb8-4ae6-a40e-c26a674f4732
-- title:
--   Theorem 7.3 — online conditional gradient regret bound (goal)
-- statement:
--   **Statement (Theorem 7.3, p. 133, PDF p. 155).** Online conditional gradient (Algorithm
--   27) with parameters $\eta = D/(2GT^{3/4})$, $\sigma_t = \min\{1, 2/\sqrt t\}$ attains
--   $$\mathrm{Regret}_T = \sum_{t=1}^T f_t(x_t) - \min_{x^\star\in K}\sum_{t=1}^T f_t(x^\star)
--   \le 8DGT^{3/4}.$$
--
--   Algorithm 27 is the chapter's payoff: an OCO algorithm with the same $\tilde O(T^{3/4})$-
--   style regret flavor as the bandit algorithms of Chapter VI, but here trading regret rate
--   for the ability to replace every Euclidean projection with a linear-minimization oracle
--   call — cheap for the matrix-completion, routing, ranking, and matroid examples the chapter
--   develops. The proof reduces to Lemma 7.4's per-round bound plus a comparison (via strong
--   convexity of $F_t$) between the algorithm's iterates and the RFTL-style minimizers
--   $x^\star_t$ of the aggregate function.
--
--   **Formalization Note.** $K$ (convex, nonempty, diameter $\le D$) and the costs $f$,
--   convex and $G$-Lipschitz on $K$, are this chapter's standing hypotheses, stated explicitly
--   — convexity of each $f_t$ is used by the proof's reduction (PDF 155–156) to Theorem 5.2
--   applied to the shifted sequence $\tilde f_t(x) = f_t(x + (x^\star_t - x_t))$, which needs
--   $f_t$ convex for $\tilde f_t$ to be convex.
--   $\min_{x^\star\in K}$ is rendered as an infimum. Rounds are summed over `Finset.Icc 1 T`,
--   matching the book's own $t=1,\dots,T$ indexing directly (this chapter keeps `t` 1-indexed
--   throughout, rather than the 0-indexed `Finset.range` shift used elsewhere in the series,
--   since Algorithm 27's own line 4 sums $\tau = 1$ to $t-1$ and reads most naturally this
--   way — see `MODERATION_NOTES.md`). The constant `8` is the book's own, unrounded.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 133, Theorem 7.3 (PDF p. 155)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

namespace OnlineConvexOpt.ProjectionFree

/-- Theorem 7.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 133, PDF p. 155). Online conditional gradient (Algorithm 27) with
parameters `η = D/(2GT^{3/4})`, `σ_t = min{1, 2/√t}` attains
`Regret_T = Σ_{t=1}^T f_t(x_t) - min_{x⋆∈K} Σ_{t=1}^T f_t(x⋆) ≤ 8DGT^{3/4}`.

`K` (convex, nonempty, diameter `≤ D`) and the costs `f`, convex and `G`-Lipschitz on `K`, are the
chapter-wide standing hypotheses of §7.5, stated here as explicit hypotheses — convexity of each
`f t` is used by the proof's reduction (PDF 155–156) to Theorem 5.2 applied to the shifted
sequence `f̃_t = f_t(x + (x⋆_t - x_t))`, which needs `f_t` convex for `f̃_t` to be convex.
`min_{x⋆∈K}` is rendered as an infimum. -/
theorem ocg_regret
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (gradf : ℕ → E) (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v) :
    (∑ t ∈ Finset.Icc 1 T, f t (x t)) - ⨅ xstar ∈ K, ∑ t ∈ Finset.Icc 1 T, f t xstar ≤
      8 * D * G * (T : ℝ) ^ (3 / 4 : ℝ) := by sorry

end OnlineConvexOpt.ProjectionFree
