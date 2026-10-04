-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_lojasiewicz_continuous_subanalytic
-- name    : NonsmoothLojasiewicz.Continuous.lojasiewicz_continuous_subanalytic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:15:39.178985+00:00
-- url     : https://prove2.me/theorems/c2c9aa25-f45e-40b4-a601-98c6eeb1c8db
-- title:
--   Theorem 3.1: the Łojasiewicz inequality at critical points of continuous subanalytic functions
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$ be a subanalytic function with closed domain, and assume that $f|_{\operatorname{dom} f}$ is continuous. Let $a \in \mathbb{R}^n$ be a critical point of $f$, i.e. $0 \in \partial f(a)$ for the limiting subdifferential $\partial f$. Then there exists an exponent $\theta \in [0, 1)$ such that the function
--   $$
--   \frac{|f - f(a)|^{\theta}}{m_f}
--   $$
--   is bounded around $a$, where $m_f(x) = \inf\{\|x^*\| : x^* \in \partial f(x)\}$ is the nonsmooth slope and the conventions $0^0 = 1$ and $\infty/\infty = 0/0 = 0$ are adopted. Equivalently, there are $C \in \mathbb{R}$ and a neighbourhood $U$ of $a$ with
--   $$
--   |f(x) - f(a)|^{\theta} \le C\, \|x^*\| \qquad \text{for all } x \in U,\ x^* \in \partial f(x).
--   $$
--
--   This extends the classical Łojasiewicz gradient inequality for real-analytic functions to nonsmooth subanalytic functions, with the limiting subdifferential in place of the gradient. It is the basic tool for proving finite length and convergence of subgradient trajectories and of descent methods.
--
--   **Formalization Note.** `f : EuclideanSpace ℝ (Fin n) → EReal` with `f x ≠ ⊥`; closed domain `{x | f x ≠ ⊤}`; `ContinuousOn f` on the domain; subanalyticity via the graph over the real values (Definition 2.1). The boundedness of the ratio is the predicate `LojIneqAt f a θ` (division-free form, `Real.rpow` with `0 ^ 0 = 1`); in particular $\theta = 0$ can never work at a critical point, as under the paper's conventions. No lower semicontinuity, real-valuedness, global subanalyticity or compactness of the critical set is assumed.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1213 (PDF p. 9), Theorem 3.1, with the conventions stated after (8)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_NonsmoothLojasiewicz_Continuous_LojIneqAt

open Filter Topology
open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- Theorem 3.1 (p. 1213): let `f : ℝⁿ → ℝ ∪ {+∞}` be subanalytic with closed domain and
continuous on its domain, and let `a` be a critical point of `f`. Then there is `θ ∈ [0, 1)`
such that `|f − f(a)|^θ / m_f` is bounded around `a` (conventions `0^0 = 1`,
`∞/∞ = 0/0 = 0`), encoded as `LojIneqAt f a θ`. -/
theorem lojasiewicz_continuous_subanalytic {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ crit f) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ LojIneqAt f a θ := by sorry

end NonsmoothLojasiewicz.Continuous
