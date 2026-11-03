-- Prove2me | Theorems.Thm_MonoInclCLC_lemma_2_10
-- name    : MonoInclCLC.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:05.874206+00:00
-- url     : https://prove2.me/theorems/0f76f58a-998b-4eae-94e4-60f40afe6b9b
-- title:
--   Lemma 2.10, p.9 — the feedback law $\lambda(\cdot)$ is nondecreasing
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. Let $\theta>0$, let $p\ge 1$ be an integer, let $t_0>0$, and let $(x,\lambda):[0,t_0]\to\mathcal H\times(0,+\infty)$ be a solution of the closed-loop control system with $x(0)\notin A^{-1}(0)$. Then $\lambda(\cdot)$ is nondecreasing on $[0,t_0]$.
--
--   Since $\lambda(t)\|\dot x(t)\|^{p-1}=\theta$, this says that the speed of the trajectory does not increase, which is the fact behind the pointwise rates.
--
--   Differences from the source:
--   - generalization: θ ∈ (0, 1) in §2 (Eq. (2.1)) → θ > 0; reason: Eq. (1.4) itself has θ > 0 and no step uses θ < 1; the case θ ∈ (0, 1) is included
--   - generalization: a solution, for which the paper also records x continuously differentiable and λ locally Lipschitz (Theorems 2.4, 2.6) → IsClosedLoopSolution: λ > 0 and Eqs. (1.3), (1.4) at every time, x differentiable, no regularity requirement; reason: every solution in the paper's sense is one here, so the statement specializes to the source; the paper's proofs use only differentiability
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
--   - encoding: (1.4) written with ‖ẋ(t)‖ → (1.4) written with ‖(I + λ(t)A)⁻¹x(t) − x(t)‖; reason: the paper's own form on p.5, equal under (1.3)
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Lemma 2.10, p.9

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_IsClosedLoopSolution

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **Lemma 2.10** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Lemma 2.10, p.9): if `(x, λ) : [0, t₀] ↦ H × (0, +∞)` is a solution of the
closed-loop control system (1.3)–(1.4), then `λ(·)` is nondecreasing.

**Formalization Note.** `J l` is the resolvent `(I + l A)⁻¹` for `l > 0`. The time set of the solution is `Set.Icc 0 t₀`. Every `p ≥ 1` is covered (`p = 1` gives
`λ ≡ θ`). -/
theorem lemma_2_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (x : ℝ → H) (lam : ℝ → ℝ)
    (hsol : IsClosedLoopSolution J p θ (Set.Icc 0 t₀) x lam) (hx0 : x 0 ∉ zer A) :
    MonotoneOn lam (Set.Icc 0 t₀) := by sorry

end MonoInclCLC
