-- Prove2me | Theorems.Thm_LearnStability_ConvexSCO_strongConvex_minimizer_growth
-- name    : LearnStability.ConvexSCO.strongConvex_minimizer_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:14:46.118186+00:00
-- url     : https://prove2.me/theorems/e1f56643-68ce-4d0b-9e61-f1997a438342
-- title:
--   Quadratic growth of a λ-strongly convex function at its minimizer over a set
-- statement:
--   Let $\mathcal H$ be a subset of a real Hilbert space and $\lambda\ge0$. A function $g:\mathcal H\to\mathbb R$ is **$\lambda$-strongly convex** on $\mathcal H$ if $g-\frac\lambda2\|\cdot\|^2$ is convex there. If $g$ is $\lambda$-strongly convex on $\mathcal H$ and $h\in\mathcal H$ minimizes $g$ over $\mathcal H$, then for every $h'\in\mathcal H$
--   $$g(h')-g(h)\ \ge\ \frac\lambda2\,\|h'-h\|^2 .$$
--
--   This quadratic growth is what turns a small change in the empirical objective into a small change in its minimizer, the first step of the stability argument for Theorem 2.
--
--   **Formalization Note** Strong convexity is Mathlib's `StrongConvexOn Hset λ g`, which in an inner product space is equivalent to convexity of $g-\frac\lambda2\|\cdot\|^2$ on $\mathcal H$ (`strongConvexOn_iff_convex`); it includes convexity of $\mathcal H$.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2644, §4.2, display after the definition of λ-strong convexity

import Mathlib

namespace LearnStability.ConvexSCO

/-- §4.2, display after the definition of λ-strong convexity (p. 2644): if `g` is
`λ`-strongly convex on a domain `H` of a Hilbert space (`λ ≥ 0`) and `h ∈ H` minimizes `g`
over `H`, then `g(h') − g(h) ≥ (λ/2)‖h' − h‖²` for every `h' ∈ H`. Mathlib's
`StrongConvexOn Hset λ g` is the paper's definition (`g − (λ/2)‖·‖²` convex on `Hset`). -/
theorem strongConvex_minimizer_growth {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {lam : ℝ} (hlam : 0 ≤ lam)
    {g : E → ℝ} (hg : StrongConvexOn Hset lam g) {h : E} (hh : h ∈ Hset)
    (hmin : ∀ h' ∈ Hset, g h ≤ g h') :
    ∀ h' ∈ Hset, lam / 2 * ‖h' - h‖ ^ 2 ≤ g h' - g h := by sorry

end LearnStability.ConvexSCO
