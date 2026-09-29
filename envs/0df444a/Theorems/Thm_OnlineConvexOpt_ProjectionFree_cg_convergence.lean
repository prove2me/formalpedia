-- Prove2me | Theorems.Thm_OnlineConvexOpt_ProjectionFree_cg_convergence
-- name    : OnlineConvexOpt.ProjectionFree.cg_convergence
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:43:47.805487+00:00
-- url     : https://prove2.me/theorems/1e270e51-9d90-4c62-84c4-b1d3c675ac0b
-- title:
--   Theorem 7.1 — offline conditional gradient convergence rate
-- statement:
--   **Statement (Theorem 7.1, p. 127, PDF p. 149).** The conditional gradient algorithm
--   (Algorithm 25) applied to $\beta$-smooth functions with step sizes $\eta_t = \min\{1,
--   2/t\}$ attains $h_t \le 2\beta D^2/t$ for every $t \ge 1$, where $h_t = f(x_t) - f(x^\star)$
--   and $D$ is the diameter of $K$.
--
--   This is the offline convergence guarantee the online algorithm's own analysis (Lemma 7.4,
--   Theorem 7.3) reduces to, applied there to the aggregate function $F_t$ rather than to any
--   single $f_t$.
--
--   **Formalization Note.** $K$ (convex, nonempty, diameter $\le D$), $f$ (convex and
--   $\beta$-smooth with gradient map $g$ — §7.3's own setup, "minimizing a smooth convex
--   function $f$ over a convex set $K$", used explicitly in the proof's Eq. (7.2) step), and
--   $x^\star$ (a global minimizer of $f$ over $K$) are this theorem's own explicit hypotheses
--   (the book's standing setup for this section). Rounds are indexed from $1$, matching the
--   book directly, since the bound is per-round rather than cumulative.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 127, Theorem 7.1 (PDF p. 149)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_ConditionalGradient
import Definitions.Def_OnlineConvexOpt_ProjectionFree_SmoothOn

namespace OnlineConvexOpt.ProjectionFree

/-- Theorem 7.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 127, PDF p. 149). The (offline) conditional gradient algorithm
(Algorithm 25) applied to `β`-smooth functions with step sizes `η_t = min{1, 2/t}` attains
`h_t ≤ 2βD²/t` for every `t ≥ 1`, where `h_t = f(x_t) - f(x⋆)` and `D` is the diameter of `K`.

`K` (convex, nonempty, diameter `≤ D`), `f` (convex and `β`-smooth on `K` with gradient map `g`,
§7.3's own setup, "minimizing a smooth convex function `f` over a convex set `K`", p. 126, PDF
148 — convexity used explicitly in the proof's Eq. (7.2) step, PDF 149), and `x⋆` (a global
minimizer of `f` over `K`) are the chapter's standing hypotheses for this theorem (p. 126-127),
stated here as explicit hypotheses. -/
theorem cg_convergence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : E → ℝ) (g : E → E) (β : ℝ) (hβpos : 0 < β) (hsmooth : SmoothOn K f g β)
    (hfconv : ConvexOn ℝ K f)
    (xstar : E) (hxstar : xstar ∈ K) (hxstar_min : ∀ x ∈ K, f xstar ≤ f x)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η t = min 1 (2 / (t : ℝ)))
    (x v : ℕ → E) (hrun : IsConditionalGradientRun K g η x v)
    (t : ℕ) (ht : 1 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * D ^ 2 / t := by sorry

end OnlineConvexOpt.ProjectionFree
