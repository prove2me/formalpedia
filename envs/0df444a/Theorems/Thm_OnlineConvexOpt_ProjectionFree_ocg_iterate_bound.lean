-- Prove2me | Theorems.Thm_OnlineConvexOpt_ProjectionFree_ocg_iterate_bound
-- name    : OnlineConvexOpt.ProjectionFree.ocg_iterate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:44:20.700986+00:00
-- url     : https://prove2.me/theorems/4aa8a100-279d-427e-b018-21ba09e16f26
-- title:
--   Lemma 7.4 — per-round iterate bound for online conditional gradient
-- statement:
--   **Statement (Lemma 7.4, p. 133, PDF p. 155).** The iterates $x_t$ of Algorithm 27 satisfy,
--   for all $t \ge 1$, $h_t \le 2D^2\sigma_t$, where $h_t = F_t(x_t) - F_t(x^\star_t)$ and
--   $x^\star_t = \arg\min_{x\in K} F_t(x)$.
--
--   This is the main technical lemma Theorem 7.3's proof rests on: it bounds how far the
--   algorithm's actual iterate $x_t$ is (in $F_t$-value) from the aggregate function's own
--   minimizer, using the offline Frank-Wolfe analysis (Theorem 7.1's proof technique, via Eq.
--   (7.2)) applied to $F_t$ itself.
--
--   **Formalization Note.** The book proves this lemma specifically for Theorem 7.3's
--   parameters $\eta = D/(2GT^{3/4})$, $\sigma_t = \min\{1, 2/\sqrt t\}$ and a $G$-Lipschitz
--   cost sequence (the induction step's algebraic derivation, Eq. (7.6), explicitly uses these
--   values); these are kept as explicit hypotheses rather than treating the lemma as fully
--   parameter-free, matching how the book actually proves and uses it — see
--   `MODERATION_NOTES.md`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 133, Lemma 7.4 (PDF p. 155)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_AggregateFunction

namespace OnlineConvexOpt.ProjectionFree

/-- Lemma 7.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 133, PDF p. 155). The iterates `x_t` of Algorithm 27 satisfy, for all
`t ≥ 1`, `h_t ≤ 2D²σ_t`, where `h_t = F_t(x_t) - F_t(x⋆_t)` and `x⋆_t = arg min_{x∈K} F_t(x)`.

The book proves this lemma "as a first step in analyzing Algorithm 27" (§7.5), for the specific
parameters `η = D/(2GT^{3/4})` and `σ_t = min{1, 2/√t}` that Theorem 7.3 uses (the induction
step's algebraic derivation, Eq. (7.6), explicitly invokes these values and a `G`-Lipschitz
bound on the cost functions); these are kept as explicit hypotheses here rather than treating
the lemma as fully parameter-free, matching how the book actually proves and uses it. -/
theorem ocg_iterate_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (G : ℝ) (hGpos : 0 < G)
    (f : ℕ → E → ℝ) (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (gradf : ℕ → E) (x1 : E) (hx1 : x1 ∈ K)
    (T : ℕ) (hT : 1 ≤ T)
    (η : ℝ) (hη : η = D / (2 * G * (T : ℝ) ^ (3 / 4 : ℝ)))
    (σ : ℕ → ℝ) (hσ : ∀ t : ℕ, 1 ≤ t → σ t = min 1 (2 / Real.sqrt t))
    (x v : ℕ → E) (hrun : IsOnlineConditionalGradientRun K f gradf x1 η σ x v)
    (xstar : ℕ → E)
    (hxstar : ∀ t : ℕ, 1 ≤ t → xstar t ∈ K ∧
      ∀ y ∈ K, AggregateFunction gradf x1 η t (xstar t) ≤ AggregateFunction gradf x1 η t y)
    (t : ℕ) (ht : 1 ≤ t) :
    AggregateFunction gradf x1 η t (x t) - AggregateFunction gradf x1 η t (xstar t) ≤
      2 * D ^ 2 * σ t := by sorry

end OnlineConvexOpt.ProjectionFree
