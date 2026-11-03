-- Prove2me | Theorems.Thm_NearestDSM_theorem_3_17
-- name    : NearestDSM.theorem_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:15.388318+00:00
-- url     : https://prove2.me/theorems/7ecc6a93-621e-4142-8e9a-1ed678f8b523
-- title:
--   Theorem 3.17 — local Q-quadratic convergence of the modified semismooth Newton method
-- statement:
--   Let $\hat X\in\mathbb R^{n\times n}$ be arbitrary ($n\ge 1$), and let $[y^*]=\{y\in\mathbb R^{2n-1}: F(y)=0\}$ be the solution set of the optimality conditions of the nearest doubly stochastic matrix problem. Then:
--
--   1. $[y^*]$ is nonempty, convex and compact;
--   2. there is $\epsilon>0$ such that, for every choice of vertices in step 3, every run $y^0,y^1,\dots$ of Algorithm 3.1 with
--   $$
--   \mathrm{dist}(y^0,[y^*])<\epsilon
--   $$
--   converges to a point $\bar y\in[y^*]$, and the convergence is Q-quadratic: for some $M>0$,
--   $$
--   \|y^{k+1}-\bar y\|\le M\,\|y^k-\bar y\|^2\quad\text{for all sufficiently large }k .
--   $$
--
--   The method converges Q-quadratically although the generalized Jacobian at the solution may contain only singular matrices (whenever $X^*$ is disconnected, for example a permutation matrix) and the local error bound condition fails.
--
--   **Formalization Note** Algorithm 3.1 is run with tolerance $0$ (the iterate stays put once $F(y^k)=0$), and step 3 may pick any vertex of $[y^k]$; $\epsilon$ is chosen before the vertex choice. Q-quadratic convergence (p.6: $y^k\to y^*$ and $\limsup_k\|y^{k+1}-y^*\|/\|y^k-y^*\|^2<M$) is stated as convergence plus an eventual inequality.
--
--   Differences from the source:
--   - reading: tolerance $\mathrm{tol}$ → $\mathrm{tol}=0$, the iterate stays put once $F(y^k)=0$; reason: the convergence theorem is about the exact algorithm; with $\mathrm{tol}=0$ the while-guard stops exactly at solutions, and without a stop a vertex choice could cycle between two vertices of $[y^*]$
--   - generalization: the vertex $\tilde y^k$ "found using Theorem 3.15" → any vertex selector, with $\epsilon$ uniform over selectors; reason: the proof lets $\tilde y^k$ be "any vertex of $[y^k]$"; the procedure of Theorem 3.15 is one selector
--   - reading: "the (compact, convex) solution set $[y^*]$" → nonemptiness, convexity and compactness are stated as clauses of the conclusion; reason: the parenthetical is a claim of the theorem, and $[y^*]$ names the class of a solution $y^*$ (nonempty by Theorem 1.1)
--   - encoding: "the current iterate $y^k$" → the starting point $y^0$ of the run; reason: the iteration is time-homogeneous
--   - encoding: $\limsup_k\|y^{k+1}-y^*\|/\|y^k-y^*\|^2<M$ → $\|y^{k+1}-\bar y\|\le M\|y^k-\bar y\|^2$ for all large $k$; reason: equivalent for an existential $M$, and avoids $0/0$ when $y^k=\bar y$
--   - encoding: size $n\ge1$ → `n + 1`, Euclidean norm on `Dual n`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Theorem 3.17, p.24 (Algorithm 3.1, p.20; Q-quadratic convergence, p.6)

import Mathlib
import Definitions.Def_NearestDSM_solSet
import Definitions.Def_NearestDSM_IsVertexSelector
import Definitions.Def_NearestDSM_newtonStep
open Filter Topology

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Theorem 3.17, p.24. Let the current iterate `y^k` be sufficiently close to
the (compact, convex) solution set `[y∗]`. Then the modified Newton method (Algorithm 3.1, p.20)
converges, and at a Q-quadratic rate, to a point in `[y∗]`.

Precisely: the solution set `{y | F(y) = 0}` is nonempty, convex and compact; and there is
`ε > 0` such that, for every choice of vertices `σ`, every run `y⁰, y¹, …` of Algorithm 3.1 with
`dist(y⁰, [y∗]) < ε` converges to a point `ȳ` of the solution set, with
`‖y^{k+1} − ȳ‖ ≤ M ‖y^k − ȳ‖²` for all large `k`, for some `M > 0`.

**Formalization Note.** Algorithm 3.1 is run with `tol = 0` (`newtonStep`: the iterate stays put
once `F(y^k) = 0`) and with any vertex selector `σ` (step 3), and `ε` is chosen before `σ`. "The
current iterate" is the starting point `y 0` (the iteration is time-homogeneous). Q-quadratic
convergence (p.6: `y^k → y∗` and `limsup ‖y^{k+1} − y∗‖ / ‖y^k − y∗‖² < M`) is stated as
convergence plus an eventual inequality, which avoids `0/0` when `y^k = ȳ`. `dist` is
`Metric.infDist`, the norm Euclidean, and the paper's size `n ≥ 1` is `n + 1`. -/
theorem theorem_3_17 (n : ℕ) (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ((solSet Xh).Nonempty ∧ Convex ℝ (solSet Xh) ∧ IsCompact (solSet Xh)) ∧
      ∃ ε > (0 : ℝ), ∀ σ : Dual n → Dual n, IsVertexSelector Xh σ →
        ∀ y : ℕ → Dual n, (∀ k, y (k + 1) = newtonStep Xh σ (y k)) →
          Metric.infDist (y 0) (solSet Xh) < ε →
            ∃ ybar ∈ solSet Xh, Tendsto y atTop (𝓝 ybar) ∧
              ∃ M > (0 : ℝ), ∀ᶠ k in atTop, ‖y (k + 1) - ybar‖ ≤ M * ‖y k - ybar‖ ^ 2 := by sorry

end NearestDSM
