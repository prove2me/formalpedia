-- Prove2me | Theorems.Thm_MonoInclCLC_eq_3_8
-- name    : MonoInclCLC.eq_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:03.256877+00:00
-- url     : https://prove2.me/theorems/b60b0018-db4a-477a-a8db-e7524d311e51
-- title:
--   Eq. (3.8), p.18 — $\|x(t)-z(t)\|^2\le\mathcal E(0)/t$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. Let $\theta>0$, let $p\ge 1$ be an integer, and let $(x,\lambda):[0,+\infty)\to\mathcal H\times(0,+\infty)$ be a global solution of the closed-loop control system
--   $$
--   \dot x(t)+x(t)-(I+\lambda(t)A)^{-1}x(t)=0,\qquad \lambda(t)\,\|\dot x(t)\|^{p-1}=\theta,
--   $$
--   with $x(0)=x_0\notin A^{-1}(0)$. Write $z(t)=(I+\lambda(t)A)^{-1}x(t)$, and for $z^\star\in A^{-1}(0)$ let $\mathcal E(0)=\frac12\|x_0-z^\star\|^2$. Then, for every $z^\star\in A^{-1}(0)$ and every $t>0$,
--   $$
--   \|x(t)-z(t)\|^2\le\frac{\mathcal E(0)}{t}.
--   $$
--   This is the pointwise decay of the fixed-point residual, used both for the residue rate and for the lower bound on $\lambda$.
--
--   Differences from the source:
--   - generalization: a solution, for which the paper also records x continuously differentiable and λ locally Lipschitz (Theorems 2.4, 2.6) → IsClosedLoopSolution: λ > 0 and Eqs. (1.3), (1.4) at every time, x differentiable, no regularity requirement; reason: every solution in the paper's sense is one here, so the statement specializes to the source; the paper's proofs use only differentiability
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
--   - encoding: (1.4) written with ‖ẋ(t)‖ → (1.4) written with ‖(I + λ(t)A)⁻¹x(t) − x(t)‖; reason: the paper's own form on p.5, equal under (1.3)
--   - encoding: for all t ≥ 0 → t > 0; reason: at t = 0 the right side is a division by zero and has no meaning
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Eq. (3.8), p.18, from the proof of Theorem 3.1, p.14

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_IsClosedLoopSolution

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **Eq. (3.8)** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Eq. (3.8), p.18, from the proof of Theorem 3.1, p.14): along a global
solution, with `z(t) = (I + λ(t)A)⁻¹x(t)`, `‖x(t) - z(t)‖² ≤ E(0)/t`, where `E(0) = ½‖x₀ - z⋆‖²`
for `z⋆ ∈ A⁻¹(0)`.

**Formalization Note.** `E` is the function of the proof of Theorem 3.1, for any fixed
`z⋆ ∈ A⁻¹(0)`. The printed range `t ≥ 0` is read as `t > 0`: at `t = 0` the right side is a
division by `0`. Every `p ≥ 1` is covered. -/
theorem eq_3_8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ)
    (x : ℝ → H) (lam : ℝ → ℝ)
    (hsol : IsClosedLoopSolution J p θ (Set.Ici 0) x lam) (hx0 : x 0 ∉ zer A)
    (zs : H) (hzs : zs ∈ zer A) (t : ℝ) (ht : 0 < t) :
    ‖x t - J (lam t) (x t)‖ ^ 2 ≤ ((1 / 2 : ℝ) * ‖x 0 - zs‖ ^ 2) / t := by sorry

end MonoInclCLC
