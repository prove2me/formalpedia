-- Prove2me | Theorems.Thm_MonoInclCLC_lemma_3_4
-- name    : MonoInclCLC.lemma_3_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:20:09.24126+00:00
-- url     : https://prove2.me/theorems/b0dbe5c0-f4b6-4b23-8897-1e3cbe6905fd
-- title:
--   Lemma 3.4, p.13 — descent of $\mathcal E(t)=\frac12\|x(t)-z\|^2$ for $z\in A^{-1}(0)$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. Let $\theta>0$, let $p\ge 1$ be an integer, and let $(x,\lambda):[0,+\infty)\to\mathcal H\times(0,+\infty)$ be a global solution of the closed-loop control system
--   $$
--   \dot x(t)+x(t)-(I+\lambda(t)A)^{-1}x(t)=0,\qquad \lambda(t)\,\|\dot x(t)\|^{p-1}=\theta,
--   $$
--   with $x(0)=x_0\notin A^{-1}(0)$. Let $z\in A^{-1}(0)$ and $\mathcal E(t)=\frac12\|x(t)-z\|^2$. Then $\mathcal E$ is differentiable on $[0,+\infty)$ and
--   $$
--   \frac{d\mathcal E(t)}{dt}\le-\big\|x(t)-(I+\lambda(t)A)^{-1}x(t)\big\|^2.
--   $$
--   This is the Lyapunov descent on which the rate analysis rests.
--
--   Differences from the source:
--   - generalization: a solution, for which the paper also records x continuously differentiable and λ locally Lipschitz (Theorems 2.4, 2.6) → IsClosedLoopSolution: λ > 0 and Eqs. (1.3), (1.4) at every time, x differentiable, no regularity requirement; reason: every solution in the paper's sense is one here, so the statement specializes to the source; the paper's proofs use only differentiability
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
--   - encoding: (1.4) written with ‖ẋ(t)‖ → (1.4) written with ‖(I + λ(t)A)⁻¹x(t) − x(t)‖; reason: the paper's own form on p.5, equal under (1.3)
--   - encoding: dE(t)/dt ≤ … → ∃ e, HasDerivWithinAt E e (Set.Ici 0) t ∧ e ≤ …; reason: a one-sided derivative at t = 0 and no default value of deriv
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Lemma 3.4, p.13, with E of Eq. (3.1), p.13

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_IsClosedLoopSolution

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **Lemma 3.4** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Lemma 3.4, p.13, with `E` of Eq. (3.1)): along a global solution of
(1.3)–(1.4) and for `z ∈ A⁻¹(0)`, the function `E(t) = ½‖x(t) - z‖²` satisfies
`dE(t)/dt ≤ -‖x(t) - (I + λ(t)A)⁻¹x(t)‖²`.

**Formalization Note.** `J l` is the resolvent `(I + l A)⁻¹` for `l > 0`. The derivative is stated as a `HasDerivWithinAt` fact on `Set.Ici 0` at every `t ≥ 0` (one-sided at
`t = 0`), not with `deriv`, whose junk value would make the inequality free. -/
theorem lemma_3_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ)
    (x : ℝ → H) (lam : ℝ → ℝ)
    (hsol : IsClosedLoopSolution J p θ (Set.Ici 0) x lam) (hx0 : x 0 ∉ zer A)
    (z : H) (hz : z ∈ zer A) (t : ℝ) (ht : 0 ≤ t) :
    ∃ e : ℝ, HasDerivWithinAt (fun s : ℝ => (1 / 2 : ℝ) * ‖x s - z‖ ^ 2) e (Set.Ici 0) t ∧
      e ≤ -‖x t - J (lam t) (x t)‖ ^ 2 := by sorry

end MonoInclCLC
