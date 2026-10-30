-- Prove2me | Theorems.Thm_KarimiPL_ProxGrad_eq_2_descent_lemma
-- name    : KarimiPL.ProxGrad.eq_2_descent_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:34.16512+00:00
-- url     : https://prove2.me/theorems/0df5916a-67cf-4afc-a94d-dad1eb63bc33
-- title:
--   Eq. (2): an $L$-Lipschitz gradient gives the quadratic upper bound
-- statement:
--   Let $f : \mathbb{R}^d \to \mathbb{R}$ be differentiable and suppose its gradient is $L$-Lipschitz continuous:
--   $$\|\nabla f(x) - \nabla f(y)\| \le L\|x - y\| \quad \text{for all } x, y \in \mathbb{R}^d.$$
--   Then for all $x, y \in \mathbb{R}^d$
--   $$f(y) \le f(x) + \langle \nabla f(x), y - x\rangle + \frac L2 \|y - x\|^2.$$
--
--   This is inequality (2) of Karimi, Nutini and Schmidt, the standing smoothness assumption of the paper. It is the first step of the proof of Theorem 5, and it connects the literal hypothesis "L-Lipschitz continuous gradient" of Theorem 5 to the form (2) in which the other items of this mission assume it.
--
--   **Formalization Note** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` and $\nabla$ is Mathlib's `gradient`. No sign condition on $L$ is imposed: for $d \ge 1$ the Lipschitz hypothesis forces $L \ge 0$, and for $d = 0$ the conclusion is trivial.
--
--   Differences from the source:
--   - reading: "the first derivative of f is L-Lipschitz continuous. This means that (2)" → the implication: L-Lipschitz gradient ⇒ (2); reason: the converse is false (f(x) = −x² on ℝ satisfies (2) with L = 0 but its gradient is not 0-Lipschitz), so the implication is the true content of "this means"
--   - encoding: first derivative of f exists and is L-Lipschitz → Differentiable ℝ f and ‖∇f x − ∇f y‖ ≤ L‖x − y‖ for all x, y; reason: Mathlib's gradient is 0 at points of non-differentiability, so differentiability is stated
--   - generalization: Lipschitz constant L > 0 → any real L; reason: no sign hypothesis is needed; the statement specializes to L > 0
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §2, eq. (2), p. 2

import Mathlib

open scoped InnerProductSpace

namespace KarimiPL.ProxGrad

/-- **Eq. (2): an `L`-Lipschitz gradient gives the quadratic upper bound.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, §2, eq. (2), p. 2: "we assume that the first derivative of f is L-Lipschitz continuous.
This means that f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2)||y − x||², (2) for all x and y."

If `f : ℝᵈ → ℝ` is differentiable and `‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖` for all `x, y`, then
`f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2)‖y − x‖²` for all `x, y`.

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)` and `∇` is Mathlib's `gradient`;
`Differentiable ℝ f` makes `gradient f` the true gradient. No sign condition on `L` is
needed: for `d ≥ 1` the Lipschitz hypothesis forces `L ≥ 0`, and for `d = 0` the conclusion
is trivial. -/
theorem eq_2_descent_lemma {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}
    (hf : Differentiable ℝ f)
    (hlip : ∀ x y : EuclideanSpace ℝ (Fin d), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin d)) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by sorry

end KarimiPL.ProxGrad
