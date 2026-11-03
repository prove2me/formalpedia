-- Prove2me | Theorems.Thm_MonoInclCLC_integrated_gap_inequality
-- name    : MonoInclCLC.integrated_gap_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:05.402479+00:00
-- url     : https://prove2.me/theorems/8662585c-e922-40e6-bf5c-c4fb63c42402
-- title:
--   p.18, second display of the proof of Theorem 3.7 — the integrated inequality
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. Let $\theta>0$, let $p\ge 1$ be an integer, and let $(x,\lambda):[0,+\infty)\to\mathcal H\times(0,+\infty)$ be a global solution of the closed-loop control system
--   $$
--   \dot x(t)+x(t)-(I+\lambda(t)A)^{-1}x(t)=0,\qquad \lambda(t)\,\|\dot x(t)\|^{p-1}=\theta,
--   $$
--   with $x(0)=x_0\notin A^{-1}(0)$. Write $z(s)=(I+\lambda(s)A)^{-1}x(s)$. Then, for any $z\in\mathrm{dom}(A)$, any $\xi\in Az$ and all $t\ge 0$, with $\mathcal E(t)=\frac12\|x(t)-z\|^2$,
--   $$
--   \int_0^t\lambda(s)\,\langle\xi,z(s)-z\rangle\,ds\le\mathcal E(0)-\mathcal E(t)\le\tfrac12\|x_0-z\|^2.
--   $$
--   Here $z$ is a generic point of the domain, not a zero of $A$. This choice is what makes the Lyapunov function produce a bound on the gap function.
--
--   Differences from the source:
--   - generalization: a solution, for which the paper also records x continuously differentiable and λ locally Lipschitz (Theorems 2.4, 2.6) → IsClosedLoopSolution: λ > 0 and Eqs. (1.3), (1.4) at every time, x differentiable, no regularity requirement; reason: every solution in the paper's sense is one here, so the statement specializes to the source; the paper's proofs use only differentiability
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
--   - encoding: (1.4) written with ‖ẋ(t)‖ → (1.4) written with ‖(I + λ(t)A)⁻¹x(t) − x(t)‖; reason: the paper's own form on p.5, equal under (1.3)
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, p.18, proof of Theorem 3.7, the display after "Integrating this inequality over [0, t] yields"

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_IsClosedLoopSolution

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **The integrated inequality on p.18** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, p.18, proof of Theorem 3.7, the second display):
for any `z ∈ dom(A)` and any `ξ ∈ Az`, with `z(s) = (I + λ(s)A)⁻¹x(s)` and `E(t) = ½‖x(t) - z‖²`,
`∫₀ᵗ λ(s) ⟨ξ, z(s) - z⟩ ds ≤ E(0) - E(t) ≤ ½‖x₀ - z‖²` for all `t ≥ 0`.

**Formalization Note.** `J l` is the resolvent `(I + l A)⁻¹` for `l > 0`. `x₀ = x 0`. The integrand is continuous along a solution, so the Bochner integral carries
no junk value. -/
theorem integrated_gap_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ)
    (x : ℝ → H) (lam : ℝ → ℝ)
    (hsol : IsClosedLoopSolution J p θ (Set.Ici 0) x lam) (hx0 : x 0 ∉ zer A)
    (z : H) (hz : z ∈ dom A) (ξ : H) (hξ : ξ ∈ A z) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, lam s * ⟪ξ, J (lam s) (x s) - z⟫_ℝ) ≤
        (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2 - (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 ∧
      (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2 - (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖x 0 - z‖ ^ 2 := by sorry

end MonoInclCLC
