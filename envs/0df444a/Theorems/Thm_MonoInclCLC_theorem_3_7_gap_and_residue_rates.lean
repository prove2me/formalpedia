-- Prove2me | Theorems.Thm_MonoInclCLC_theorem_3_7_gap_and_residue_rates
-- name    : MonoInclCLC.theorem_3_7_gap_and_residue_rates
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:25.229864+00:00
-- url     : https://prove2.me/theorems/588d9867-214b-490b-ba71-b2279fcb6a9e
-- title:
--   Theorem 3.7, p.16 — ergodic gap $O(t^{-(p+1)/2})$ and pointwise residue $O(t^{-p/2})$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. Let $\theta>0$, let $p\ge 1$ be an integer, and let $(x,\lambda):[0,+\infty)\to\mathcal H\times(0,+\infty)$ be a global solution of the closed-loop control system
--   $$
--   \dot x(t)+x(t)-(I+\lambda(t)A)^{-1}x(t)=0,\qquad \lambda(t)\,\|\dot x(t)\|^{p-1}=\theta,
--   $$
--   with $x(0)=x_0\notin A^{-1}(0)$. Assume moreover that $\mathrm{dom}(A)=\{x:Ax\neq\emptyset\}$ is closed and bounded. Let
--   $$
--   \mathrm{gap}(w)=\sup_{z\in\mathrm{dom}(A)}\sup_{\xi\in Az}\langle\xi,w-z\rangle,\qquad\mathrm{res}(w)=\inf_{\xi\in Aw}\|\xi\|,
--   $$
--   let $z(t)=(I+\lambda(t)A)^{-1}x(t)$ be the pointwise iterate, and let $\tilde z(t)=\big(\int_0^t\lambda(s)\,ds\big)^{-1}\int_0^t\lambda(s)\,z(s)\,ds$ be the ergodic iterate. Then there are constants $C,C'>0$, independent of $t$, such that for every $t>0$,
--   $$
--   \mathrm{gap}(\tilde z(t))\le C\,t^{-\frac{p+1}{2}},\qquad\mathrm{res}(z(t))\le C'\,t^{-\frac{p}{2}}.
--   $$
--   For $p=1$ these are the classical rates of the proximal point flow, and each increase of $p$ improves both rates by a factor $t^{-1/2}$. The theorem is the continuous-time counterpart of the rates of high-order methods for monotone inclusions.
--
--   **Formalization Note** The bound on the gap is stated as $\langle\xi,\tilde z(t)-z\rangle\le C\,t^{-(p+1)/2}$ for all $z\in\mathrm{dom}(A)$ and $\xi\in Az$, and the bound on the residue as the existence of $\xi\in A(z(t))$ with $\|\xi\|\le C'\,t^{-p/2}$. The constants may depend on the data and the trajectory.
--
--   Differences from the source:
--   - generalization: a solution, for which the paper also records x continuously differentiable and λ locally Lipschitz (Theorems 2.4, 2.6) → IsClosedLoopSolution: λ > 0 and Eqs. (1.3), (1.4) at every time, x differentiable, no regularity requirement; reason: every solution in the paper's sense is one here, so the statement specializes to the source; the paper's proofs use only differentiability
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
--   - encoding: (1.4) written with ‖ẋ(t)‖ → (1.4) written with ‖(I + λ(t)A)⁻¹x(t) − x(t)‖; reason: the paper's own form on p.5, equal under (1.3)
--   - reading: a = O(b(k)): a ≤ C · b(k) with C > 0 independent of k, defined for an iteration count k ≥ 1 (p.4) → ∃ C > 0, ∀ t > 0, with C after the data and the trajectory; reason: the paper applies O(·) to a continuous time; the stronger reading, every t > 0 and not only large t, is the one its proof gives
--   - encoding: gap(w) = sup sup ⟨ξ, w − z⟩ ≤ c → ∀ z ∈ dom A, ∀ ξ ∈ A z, ⟪ξ, w − z⟫ ≤ c; reason: equivalent to the supremum bound, with no default value of a real supremum
--   - encoding: res(w) = inf_{ξ∈Aw} ‖ξ‖ ≤ c → ∃ ξ ∈ A w, ‖ξ‖ ≤ c; reason: A w is closed and convex for maximal monotone A, so the infimum is attained and the forms are equivalent
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Theorem 3.7, p.16 (O(·) as defined on p.4; gap Eq. (3.3), res Eq. (3.4), p.16)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_IsClosedLoopSolution
import Definitions.Def_MonoInclCLC_ergodicIterate

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **Theorem 3.7** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Theorem 3.7, p.16): let `(x, λ) : [0, +∞) ↦ H × (0, +∞)` be a global
solution of the closed-loop control system (1.3)–(1.4), and let `dom(A)` be closed and bounded. Then
`gap(z̃(t)) = O(t^(-(p+1)/2))` and `res(z(t)) = O(t^(-p/2))`, where `z̃(t)` is the ergodic iterate and
`z(t) = (I + λ(t)A)⁻¹x(t)` the pointwise iterate.

**Formalization Note.** `gap(w) = sup_{z ∈ dom(A)} sup_{ξ ∈ Az} ⟨ξ, w - z⟩` (Eq. (3.3)) and
`res(w) = inf_{ξ ∈ Aw} ‖ξ‖` (Eq. (3.4)). `gap(w) ≤ c` is stated as
`∀ z ∈ dom A, ∀ ξ ∈ A z, ⟪ξ, w - z⟫_ℝ ≤ c` and `res(w) ≤ c` as `∃ ξ ∈ A w, ‖ξ‖ ≤ c`, so no junk real
`⨆`/`⨅` occurs. `O(·)` is the convention of p.4: `∃ C > 0, ∀ t > 0`, with `C` independent of `t`,
`z` and `ξ`. `C` may depend on the data and the trajectory, as in the paper's proof, hence the
`∃ C` after them. The bounds hold for every `t > 0`, not only for large `t`. Exponents are real
powers. -/
theorem theorem_3_7_gap_and_residue_rates {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ)
    (x : ℝ → H) (lam : ℝ → ℝ)
    (hsol : IsClosedLoopSolution J p θ (Set.Ici 0) x lam) (hx0 : x 0 ∉ zer A)
    (hclosed : IsClosed (dom A)) (hbdd : Bornology.IsBounded (dom A)) :
    (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ z ∈ dom A, ∀ ξ ∈ A z,
      ⟪ξ, ergodicIterate J x lam t - z⟫_ℝ ≤ C * t ^ (-(((p : ℝ) + 1) / 2))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      ∃ ξ ∈ A (J (lam t) (x t)), ‖ξ‖ ≤ C * t ^ (-((p : ℝ) / 2))) := by sorry

end MonoInclCLC
