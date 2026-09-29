-- Prove2me | Theorems.Thm_OnlineConvexOpt_GamesDuality_simple_lp_regret
-- name    : OnlineConvexOpt.GamesDuality.simple_lp_regret
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-18T05:22:13.586265+00:00
-- url     : https://prove2.me/theorems/e3dc1f85-3872-420c-889d-b7b9898d9b3b
-- title:
--   Lemma 8.4 — Algorithm 28's output is a √(2 log n)/√T-approximate LP solution
-- statement:
--   **Lemma 8.4** (p. 147), the goal of this mission: Algorithm 28 ("Simple LP") is a concrete,
--   regret-minimization-based algorithm that computes an approximate equilibrium of a zero-sum
--   game — and, via the equivalence of Section 8.2.1, an approximate solution to the linear
--   program the game encodes — at an explicit, quantitative rate.
--
--   Let $A \in \mathbb{R}^{n \times m}$ ($n, m \ge 1$), let $T \ge 1$, and let $(x, y)$ be a run of
--   Algorithm 28 on $A$ with learning rate $\eta = \sqrt{2 \log n / T}$ (`IsSimpleLPRun`, as in
--   the regret bound above). Let $\bar{x}$ be the algorithm's returned vector, the average of
--   $x_0, \dots, x_{T-1}$. Then, for every column strategy $y' \in \Delta_m$,
--   $$\bar{x}^{\mathsf T} A y' \;\le\; \lambda_R(A) + \frac{\sqrt{2 \log n}}{\sqrt{T}}.$$
--   Equivalently, $\max_{y' \in \Delta_m} \bar{x}^{\mathsf T} A y' \le \lambda_R(A) +
--   \sqrt{2\log n}/\sqrt{T}$: the book calls $\bar{x}$ a "$\sqrt{2 \log n}/\sqrt{T}$-approximate
--   solution" to the game and the linear program it describes, in exactly this sense. Consequently,
--   to reach an $\varepsilon$-approximate solution, $T = 2 \log n / \varepsilon^2$ rounds suffice,
--   each a single multiplicative-weights update — the chapter's efficient algorithm for
--   approximating both the game's value and the underlying linear program.
--
--   **Formalization Note.** The book states the bound against $\lambda^\star = \lambda_C = \lambda_R$
--   (the common value guaranteed to exist by Theorem 8.3, von Neumann's minimax theorem, taken in
--   this mission as the reference item `AGT.zero_sum_minimax`); the goal renders $\lambda^\star$
--   as $\lambda_R$, the quantity the algorithm's own analysis produces directly, which Theorem 8.3
--   identifies with $\lambda_C$ and hence with $\lambda^\star$. This is strictly more than
--   asserting an equilibrium exists (which `AGT.zero_sum_minimax` alone already gives): the
--   content here is that one specific, efficient, Hedge-type algorithm computes an explicit,
--   quantitatively-rated near-equilibrium.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 147, Lemma 8.4

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game

namespace OnlineConvexOpt.GamesDuality

/-- **Lemma 8.4**, Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 147: the vector `x̄` returned by Algorithm 28 after `T` rounds is a
`√(2 log n) / √T`-approximate solution to the zero-sum game (and the linear program it
describes) — meaning `max_{y ∈ Δm} x̄⊤Ay ≤ λ⋆ + √(2 log n)/√T`, rendering the book's
`λ⋆ = λ_C = λ_R` (Theorem 8.3) as `λ_R`. -/
theorem simple_lp_regret {n m T : ℕ} (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ)
    (hrun : IsSimpleLPRun (Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ))) A x y) :
    ∀ y' ∈ stdSimplex ℝ (Fin m),
      rowValue A (average x T) y' ≤
        lambdaR A + Real.sqrt (2 * Real.log (n : ℝ)) / Real.sqrt (T : ℝ) := by sorry

end OnlineConvexOpt.GamesDuality
