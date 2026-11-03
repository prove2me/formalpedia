-- Prove2me | Theorems.Thm_MonoInclCLC_ergodic_gap_bound
-- name    : MonoInclCLC.ergodic_gap_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:22.776853+00:00
-- url     : https://prove2.me/theorems/a089eeab-e990-42d9-ad12-cc236c3bdfde
-- title:
--   p.18, display before Eq. (3.7) — the ergodic gap bound
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. Let $\theta>0$, let $p\ge 1$ be an integer, and let $(x,\lambda):[0,+\infty)\to\mathcal H\times(0,+\infty)$ be a global solution of the closed-loop control system
--   $$
--   \dot x(t)+x(t)-(I+\lambda(t)A)^{-1}x(t)=0,\qquad \lambda(t)\,\|\dot x(t)\|^{p-1}=\theta,
--   $$
--   with $x(0)=x_0\notin A^{-1}(0)$. Let $\tilde z(t)$ be the ergodic iterate. Then, for any $t>0$, any $z\in\mathrm{dom}(A)$ and any $\xi\in Az$,
--   $$
--   \langle\xi,\tilde z(t)-z\rangle\le\frac{1}{\int_0^t\lambda(s)\,ds}\Big(\tfrac12\|x_0-z\|^2\Big)\le\frac{1}{\int_0^t\lambda(s)\,ds}\Big(\sup_{z\in\mathrm{dom}(A)}\|x_0-z\|^2\Big).
--   $$
--   It bounds the gap of the ergodic iterate by the inverse of the accumulated step size, so that the rate follows from a lower bound on $\lambda$.
--
--   **Formalization Note** The second inequality is stated for every upper bound $D$ of $\|x_0-z'\|^2$ over $z'\in\mathrm{dom}(A)$. No boundedness of the domain is assumed.
--
--   Differences from the source:
--   - generalization: a solution, for which the paper also records x continuously differentiable and λ locally Lipschitz (Theorems 2.4, 2.6) → IsClosedLoopSolution: λ > 0 and Eqs. (1.3), (1.4) at every time, x differentiable, no regularity requirement; reason: every solution in the paper's sense is one here, so the statement specializes to the source; the paper's proofs use only differentiability
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
--   - encoding: (1.4) written with ‖ẋ(t)‖ → (1.4) written with ‖(I + λ(t)A)⁻¹x(t) − x(t)‖; reason: the paper's own form on p.5, equal under (1.3)
--   - encoding: the display is stated at each t, and z̃(0) is 1/0 times 0 → t > 0; reason: at t = 0 the right side is a division by zero and has no meaning
--   - encoding: sup_{z∈dom(A)} ‖x₀ − z‖² → every upper bound D of ‖x₀ − z'‖² on dom A; reason: no default value of a real supremum; the clause is empty exactly when the supremum is +∞
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, p.18, proof of Theorem 3.7, the display before Eq. (3.7)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_IsClosedLoopSolution
import Definitions.Def_MonoInclCLC_ergodicIterate

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **The ergodic gap bound** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, p.18, proof of Theorem 3.7, the display before Eq. (3.7)):
for any `z ∈ dom(A)` and any `ξ ∈ Az`,
`⟨ξ, z̃(t) - z⟩ ≤ (1/∫₀ᵗ λ(s) ds) (½‖x₀ - z‖²) ≤ (1/∫₀ᵗ λ(s) ds) (sup_{z ∈ dom(A)} ‖x₀ - z‖²)`.

**Formalization Note.** `t > 0`, because `z̃(0)` is a division by `0`. The supremum of the second
inequality is written with an arbitrary upper bound `D` of `‖x₀ - z'‖²` over `z' ∈ dom(A)`, so no
junk real `⨆` occurs and the clause is empty exactly when the supremum is `+∞`. No boundedness of
`dom(A)` is assumed. -/
theorem ergodic_gap_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ)
    (x : ℝ → H) (lam : ℝ → ℝ)
    (hsol : IsClosedLoopSolution J p θ (Set.Ici 0) x lam) (hx0 : x 0 ∉ zer A)
    (t : ℝ) (ht : 0 < t) (z : H) (hz : z ∈ dom A) (ξ : H) (hξ : ξ ∈ A z) :
    ⟪ξ, ergodicIterate J x lam t - z⟫_ℝ ≤
        (∫ s in (0 : ℝ)..t, lam s)⁻¹ * ((1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2) ∧
      ∀ D : ℝ, (∀ z' ∈ dom A, ‖x 0 - z'‖ ^ 2 ≤ D) →
        (∫ s in (0 : ℝ)..t, lam s)⁻¹ * ((1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2) ≤
          (∫ s in (0 : ℝ)..t, lam s)⁻¹ * D := by sorry

end MonoInclCLC
