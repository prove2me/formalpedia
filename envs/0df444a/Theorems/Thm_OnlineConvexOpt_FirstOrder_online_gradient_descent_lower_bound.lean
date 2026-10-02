-- Prove2me | Theorems.Thm_OnlineConvexOpt_FirstOrder_online_gradient_descent_lower_bound
-- name    : OnlineConvexOpt.FirstOrder.online_gradient_descent_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:18:41.696382+00:00
-- url     : https://prove2.me/theorems/438cd41e-0ec3-4f5f-9afc-92a8c82d0426
-- title:
--   Theorem 3.2 — Ω(DG√T) worst-case regret lower bound
-- statement:
--   **Statement (Theorem 3.2).** Any algorithm for online convex optimization incurs $\Omega(DG\sqrt{T})$ regret in the worst case. The book demonstrates this by an explicit hard instance: the $n$-dimensional hypercube $K = \{x \in \mathbb{R}^n : \|x\|_\infty \le 1\}$ (diameter $D \le 2\sqrt{n}$) together with linear cost functions $f_v(x) = v^\top x$, $v \in \{\pm 1\}^n$ (gradient norm $G \le \sqrt{n}$), chosen adaptively against the algorithm (via a random vertex $v$) so that no non-anticipating algorithm can beat regret $c \cdot D G \sqrt{T}$ for an absolute constant $c > 0$.
--
--   Formally: there is an absolute constant $c > 0$ such that for every dimension $n \ge 1$ there is a decision set $K \subseteq \mathbb{R}^n$ of diameter $D$ such that, for every non-anticipating algorithm $A$ (a map from the full, a-priori-unknown cost sequence to the played decisions, constrained so round $t$'s play depends only on rounds before $t$, and always inside $K$) and every horizon $T \ge 1$, there is a sequence of convex cost functions with gradient norm at most $G$ on $K$, chosen after $A$ and $T$ are fixed, against which $A$'s regret is at least $c \cdot D \cdot G \cdot \sqrt{T}$. The quantifier order — the adversary's cost sequence depends on the algorithm, not the other way around — is exactly what "any algorithm ... incurs ... regret" means; the false converse (one fixed sequence beating every algorithm) is refuted by the constant algorithm that plays a minimizer of that one sequence and so suffers zero regret against it.
--
--   **Formalization Note.** This formalizes the theorem's main sentence — the worst-case existence claim, which is what "any algorithm ... incurs $\Omega(DG\sqrt T)$ regret in the worst case" asserts — using `IsOnlineAlgorithm` (`OnlineConvexOpt.FirstOrder.Algorithm`) to quantify over every non-anticipating algorithm, with the cost sequence existentially quantified *after* the algorithm and the horizon. It does **not** capture the theorem's parenthetical strengthening ("This is true even if the cost functions are generated from a fixed stationary distribution"), which needs a probabilistic/adaptive-adversary model (an i.i.d. random cost sequence and expected regret) that this mission leaves out for budget; see MODERATION_NOTES.md. $G$ is stated as a bound on the gradient's norm on $K$ (via `HasGradientAt`), matching the book's own definition (p. 20) rather than the weaker two-point Lipschitz condition. The instance and its diameter/gradient-norm bounds are existentially quantified rather than fixed to the book's exact hypercube construction, since the theorem's own claim is about the existence of *some* worst-case instance realizing the stated asymptotics, not about this particular one.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 45, Theorem 3.2 (PDF p. 67)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm

open OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.FirstOrder

/-- Theorem 3.2 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 45, PDF p. 67). Any online algorithm for online convex optimization
incurs `Ω(DG√T)` regret in the worst case: for every dimension `n` there is a decision set `K`
(diameter `D`) such that **for every** non-anticipating algorithm `A` and every horizon `T`,
there is a convex, subgradient-norm-`≤ G` cost sequence `f` (chosen against `A`) forcing regret
at least `c · D · G · √T`, for an absolute constant `c > 0`. The quantifier order is load-bearing:
the cost sequence is chosen *after* the algorithm (and the horizon), matching the book's actual
claim ("any algorithm ... incurs ... regret") rather than the false converse "some fixed sequence
defeats every algorithm" (a constant algorithm that always plays a minimizer of that one fixed
sequence would have zero regret against it). (We formalize the theorem's main worst-case-existence
claim; the parenthetical strengthening "even if the cost functions are generated from a fixed
stationary distribution" is not captured here — see MODERATION_NOTES.md.) -/
theorem online_gradient_descent_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (D G : ℝ), 0 < D ∧ 0 < G ∧
        Convex ℝ K ∧ IsComplete K ∧ K.Nonempty ∧ (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) ∧
        ∀ (A : (ℕ → EuclideanSpace ℝ (Fin n) → ℝ) → ℕ → EuclideanSpace ℝ (Fin n)),
          IsOnlineAlgorithm K A →
          ∀ T : ℕ, 1 ≤ T →
            ∃ f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
              (∀ t, ConvexOn ℝ K (f t)) ∧
              (∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G) ∧
              c * D * G * Real.sqrt T ≤ RegretT K f (fun t => A f t) T := by sorry

end OnlineConvexOpt.FirstOrder
