-- Prove2me | Theorems.Thm_OnlineConvexOpt_ProjectionFree_cg_convergence_v2
-- name    : OnlineConvexOpt.ProjectionFree.cg_convergence_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:22:12.767467+00:00
-- url     : https://prove2.me/theorems/cca3b18a-289b-43e2-9cc2-b0565612b863
-- title:
--   Theorem 7.1 — Conditional gradient convergence $h_t\le 2\beta D^2/t$ for $t\ge2$ (gradient map tied to $f$)
-- statement:
--   **Statement (Theorem 7.1).** Let $K$ be a nonempty convex set of diameter at most $D$ in a real Hilbert space, $f$ convex on $K$ and $\beta$-smooth on $K$ with gradient map $g=\nabla f$ (a genuine gradient at every point of $K$), and $x^\star$ a minimizer of $f$ over $K$. Run the conditional gradient algorithm (Algorithm 25) with step sizes $\eta_t=\min\{1,2/t\}$ from any $x_1\in K$. Then for every $t\ge2$,
--   $$h_t=f(x_t)-f(x^\star)\le\frac{2\beta D^2}{t}.$$
--
--   **Formalization Note.** Two corrections. (i) The printed theorem states no range for $t$, but its proof (Lemma 7.2) starts the induction from $h_2\le\beta D^2/2$ and never bounds $h_1$, which is the suboptimality of an arbitrary starting point and can exceed $2\beta D^2$ (a steep linear $f$); the statement is now for $t\ge2$, which is what the book proves. (ii) The retired statement related $g$ to $f$ only through the smoothness inequality `SmoothOn K f g β`, which does not force $g(x)$ to be a subgradient of $f$ at boundary points of $K$; the proof's convexity step $f(x^\star)\ge f(x_t)+\langle g(x_t),x^\star-x_t\rangle$ then fails and a run can stall (e.g. $K=[0,1]$, $f(y)=y$, $g(1)=0$ gives $h_t=1$ forever). The hypothesis `hg : ∀ x ∈ K, HasGradientAt f (g x) x` makes $g$ the gradient of $f$, as in the book where smoothness is stated for $\nabla f$. The standing assumptions (convexity of $K$ and $f$, diameter bound, minimizer $x^\star$) are unchanged; the result holds for every minimizer.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 127, Theorem 7.1 (PDF p. 149) — corrected transcription: range t ≥ 2, the range Lemma 7.2's induction establishes (the printed claim is false at t = 1)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_ConditionalGradient
import Definitions.Def_OnlineConvexOpt_ProjectionFree_SmoothOn

namespace OnlineConvexOpt.ProjectionFree

/-- Theorem 7.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 127, PDF p. 149). The (offline) conditional gradient algorithm
(Algorithm 25) applied to `β`-smooth convex functions with step sizes `η_t = min{1, 2/t}`
attains `h_t ≤ 2βD²/t` for every `t ≥ 2`, where `h_t = f(x_t) - f(x⋆)` and `D` is the
diameter of `K`.

`K` (convex, nonempty, diameter `≤ D`), `f` (convex and `β`-smooth on `K` with gradient map `g`,
§7.3's own setup, "minimizing a smooth convex function `f` over a convex set `K`", p. 126), and
`x⋆` (a global minimizer of `f` over `K`) are the chapter's standing hypotheses for this
theorem, stated explicitly.

Corrected version. (i) The range is `t ≥ 2`: the printed statement gives no range, but its
proof (Lemma 7.2) only establishes the recursion from `h_2 ≤ βD²/2` on, and at `t = 1` the
claim `h_1 ≤ 2βD²` is false (nothing bounds the suboptimality of an arbitrary starting point
`x_1 ∈ K`, e.g. a steep linear `f`). (ii) `g` is required to be the gradient of `f` at the
points of `K` (`hg`), as in the book where `∇f` is the gradient: the retired statement tied `g`
to `f` only through the smoothness inequality, which does not force `g(x)` to be a subgradient
at boundary points of `K`, and the proof's convexity step `f(x⋆) ≥ f(x_t) + ⟪g(x_t), x⋆ - x_t⟫`
then fails (a run can stall at a non-optimal point). -/
theorem cg_convergence_v2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : E → ℝ) (g : E → E) (hg : ∀ x ∈ K, HasGradientAt f (g x) x)
    (β : ℝ) (hβpos : 0 < β) (hsmooth : SmoothOn K f g β)
    (hfconv : ConvexOn ℝ K f)
    (xstar : E) (hxstar : xstar ∈ K) (hxstar_min : ∀ x ∈ K, f xstar ≤ f x)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η t = min 1 (2 / (t : ℝ)))
    (x v : ℕ → E) (hrun : IsConditionalGradientRun K g η x v)
    (t : ℕ) (ht : 2 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * D ^ 2 / t := by sorry

end OnlineConvexOpt.ProjectionFree
