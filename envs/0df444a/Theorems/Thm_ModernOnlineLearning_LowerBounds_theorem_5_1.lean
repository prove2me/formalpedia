-- Prove2me | Theorems.Thm_ModernOnlineLearning_LowerBounds_theorem_5_1
-- name    : ModernOnlineLearning.LowerBounds.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:33.564815+00:00
-- url     : https://prove2.me/theorems/5f9cbe9e-a9a3-4cb5-8597-9f1a8356d3e7
-- title:
--   Theorem 5.1 — deterministic OLO has regret at least √2 LD√T/4
-- statement:
--   Let $V\subseteq\mathbb R^d$ be nonempty, bounded, closed, and convex, with diameter $D=\max_{v,w\in V}\|v-w\|_2>0$. For every deterministic online linear optimization algorithm on $V$, every horizon $T\ge1$, and every loss bound $L\ge0$, there are loss vectors $g_1,\ldots,g_T$ with $\|g_t\|_2\le L$ and a competitor $u\in V$ such that
--
--   $$
--   \operatorname{Regret}_T(u)
--   =\sum_{t=1}^{T}\langle g_t,x_t\rangle
--    -\sum_{t=1}^{T}\langle g_t,u\rangle
--   \ge\frac{\sqrt2}{4}LD\sqrt T.
--   $$
--
--   Thus the worst-case regret of every deterministic algorithm has square-root growth even for linear losses on any nontrivial bounded convex feasible set.
--
--   **Formalization Note** The book does not introduce $L$ in the theorem sentence; it is quantified here as a nonnegative loss bound. The space is finite-dimensional Euclidean space, so closed and bounded $V$ is compact and the diameter is attained. The loss sequence and comparator are chosen after the algorithm, as the theorem requires.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 5.1, pp. 50–51

import Mathlib
import Definitions.Def_ModernOnlineLearning_LowerBounds_Protocol

namespace ModernOnlineLearning.LowerBounds

/-- Theorem 5.1, printed pp. 50–51. For each deterministic algorithm and
positive horizon, the adversary can choose bounded linear losses and one
feasible comparator with regret at least `√2 L D √T / 4`. -/
theorem theorem_5_1 {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVbounded : Bornology.IsBounded V) (hVconvex : Convex ℝ V)
    (hD : 0 < Metric.diam V)
    (A : ℕ → (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (hA : IsDeterministicOLOAlg V A)
    (L : ℝ) (hL : 0 ≤ L) (T : ℕ) (hT : 1 ≤ T) :
    ∃ (g : ℕ → EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)),
      u ∈ V ∧
      (∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ L) ∧
      Real.sqrt 2 * L * Metric.diam V * Real.sqrt (T : ℝ) / 4 ≤
        oloRegret A g u T := by sorry

end ModernOnlineLearning.LowerBounds
