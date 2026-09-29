-- Prove2me | Theorems.Thm_OnlineConvexOpt_SecondOrder_online_newton_step_regret
-- name    : OnlineConvexOpt.SecondOrder.online_newton_step_regret
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:34:44.361989+00:00
-- url     : https://prove2.me/theorems/ff86d286-8f99-4d13-81f2-d73b5daf4d1b
-- title:
--   Theorem 4.5 — regret of online Newton step
-- statement:
--   Let $K \subseteq \mathbb{R}^n$ ($n \ge 2$) be a decision set of diameter $D$, and let
--   $f_0, f_1, \dots$ be $\alpha$-exp-concave, $G$-gradient-bounded cost functions on $K$. Run
--   online Newton step (Algorithm 12) with parameters
--   $$
--   \gamma = \tfrac12 \min\Bigl\{\tfrac{1}{GD}, \alpha\Bigr\}, \qquad
--   \varepsilon = \frac{1}{\gamma^2 D^2} ,
--   $$
--   producing the play sequence $x_0, x_1, \dots$. Then for every horizon $T \ge 4$,
--   $$
--   \mathrm{Regret}_T(\mathrm{ONS}) \;\le\; 2\Bigl(\frac1\alpha + GD\Bigr)\, n \log T .
--   $$
--   This is the chapter's central result: exp-concave losses admit regret that is *logarithmic*
--   in the horizon $T$, at the cost of a factor of the ambient dimension $n$ that is absent
--   from the $O(\sqrt T)$ bound for general convex losses (Chapter III) — a genuine trade-off,
--   not an artifact of a loose proof, since it comes directly from bounding the determinant of
--   the $n \times n$ running matrix $A_T$. The bound applies, in particular, to the log-loss of
--   online portfolio selection that motivates the chapter, giving a fully polynomial-time
--   algorithm with logarithmic regret against the best fixed rebalanced portfolio in hindsight.
--
--   **Formalization Note** The hypothesis $n \ge 2$ follows the source's own derivation, which
--   states the bound explicitly "for $n > 1$, $T \ge 4$" immediately after combining Lemma 4.6
--   with the log-determinant bound.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 63, PDF p. 85, Theorem 4.5

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.SecondOrder

/-- Theorem 4.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 63, PDF p. 85). Online Newton step (Algorithm 12) on `α`-exp-concave
cost functions `f`, `G`-gradient-bounded, over a decision set `K` of diameter `D` in
`n`-dimensional space, run with `γ = (1/2) min{1/(GD), α}`, `ε = 1/(γ²D²)`, guarantees for
every `T ≥ 4`, `Regret_T ≤ 2(1/α + GD) n log T`. (The book's own derivation, immediately
following the proof, states the bound "for `n > 1`, `T ≥ 4`"; `hn : 2 ≤ n` records that
literally, rather than the possibly-stronger `n ≥ 1` the displayed statement alone would
suggest — see `MODERATION_NOTES.md`.) -/
theorem online_newton_step_regret (n : ℕ) (hn : 2 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (α D G : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (γ ε : ℝ) (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) (hT : 4 ≤ T) :
    RegretT K f x T ≤ 2 * (1 / α + G * D) * n * Real.log T := by sorry

end OnlineConvexOpt.SecondOrder
