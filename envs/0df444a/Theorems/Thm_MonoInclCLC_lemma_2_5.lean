-- Prove2me | Theorems.Thm_MonoInclCLC_lemma_2_5
-- name    : MonoInclCLC.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:06.389874+00:00
-- url     : https://prove2.me/theorems/92d0292f-0f4e-4672-89df-d396bc04b23b
-- title:
--   Lemma 2.5, p.6 — formula and Lipschitz bound for $\Gamma_\theta$ (corrected: $\Gamma_\theta$ is nonnegative real-valued, not $(0,+\infty)$-valued)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $A:\mathcal H\rightrightarrows\mathcal H$ a maximal monotone operator with $A^{-1}(0)=\{x:0\in Ax\}\neq\emptyset$. For an integer $p\ge 2$ let $\varphi(\lambda,x)=\lambda^{1/(p-1)}\|x-(I+\lambda A)^{-1}x\|$ for $\lambda>0$, and $\varphi(0,x)=0$. Let $\theta>0$ and let $\Lambda_\theta(x)$, for $x\notin A^{-1}(0)$, be the unique $\lambda>0$ with $\varphi(\lambda,x)=\theta^{1/(p-1)}$. Let $\Gamma_\theta$ be the function of Lemma 2.5. Then
--   $$
--   \Gamma_\theta(x)=\begin{cases}\big(1/\Lambda_\theta(x)\big)^{\frac{1}{p-1}}, & x\notin A^{-1}(0),\\ 0, & x\in A^{-1}(0),\end{cases}
--   $$
--   and $|\Gamma_\theta(x_1)-\Gamma_\theta(x_2)|\le\theta^{-1/(p-1)}\|x_1-x_2\|$ for all $x_1,x_2\in\mathcal H$.
--
--   The lemma turns the implicit feedback law into a Lipschitz function of the state, and this gives the regularity of $\lambda$ along solutions.
--
--   **Formalization Note** The first case is stated as: a solution $\lambda>0$ of $\varphi(\lambda,x)=\theta^{1/(p-1)}$ exists, and every such $\lambda$ gives the formula; uniqueness is Proposition 2.3.
--
--   Differences from the source:
--   - correction: Γθ : H ↦ (0, +∞) → Γθ real-valued, vanishing on A⁻¹(0); reason: the printed codomain contradicts the lemma's own second case: any x ∈ A⁻¹(0), which is nonempty by assumption, has Γθ(x) = 0
--   - generalization: θ ∈ (0, 1) in §2 (Eq. (2.1)) → θ > 0; reason: Eq. (1.4) itself has θ > 0 and no step uses θ < 1; the case θ ∈ (0, 1) is included
--   - encoding: the resolvent (I + λA)⁻¹ as an operator determined by A → a family J with IsResolvent l A (J l) for every l > 0; reason: for maximal monotone A such a map exists (Minty) and is unique (monotonicity), so no instance changes
--   - encoding: Λθ(x) = (ϕ(·, x))⁻¹(θ^{1/(p−1)}) → ∃ l > 0 with ϕ(l, x) = θ^{1/(p−1)}, and ∀ such l the formula holds; reason: Λθ is the unique such l by Proposition 2.3; the statement names no inverse function
--   - encoding: Γθ is Lipschitz continuous with constant θ^{−1/(p−1)} → the explicit inequality for all x₁, x₂; reason: this is the definition of the Lipschitz constant
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Lemma 2.5, p.6, with Λθ of Eq. (2.2), p.5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_phi
import Definitions.Def_MonoInclCLC_GammaTheta

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoInclCLC

/-- **Lemma 2.5** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Lemma 2.5, p.6, with `Λθ` of Eq. (2.2), p.5): for `p ≥ 2`,
`Γθ(x) = (1/Λθ(x))^(1/(p-1))` if `x ∈ Ω = H \ A⁻¹(0)`, `Γθ(x) = 0` otherwise, and `Γθ` is Lipschitz
continuous with constant `θ^(-1/(p-1))`.

**Formalization Note.** `Λθ(x)` is the unique `λ > 0` with `ϕ(λ, x) = θ^(1/(p-1))`: the first clause
says that such a `λ` exists and that `Γθ(x) = (1/λ)^(1/(p-1))` for every such `λ` (uniqueness is
Proposition 2.3). The Lipschitz property is the explicit inequality. The printed codomain
`(0, +∞)` of `Γθ` is corrected: `Γθ` is real-valued and vanishes on `A⁻¹(0)`. `θ > 0` is used
instead of the `θ ∈ (0, 1)` of §2.1. -/
theorem lemma_2_5 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 2 ≤ p)
    (θ : ℝ) (hθ : 0 < θ) :
    (∀ x : H, x ∉ zer A →
      (∃ l : ℝ, 0 < l ∧ phi J p l x = θ ^ (1 / ((p : ℝ) - 1))) ∧
      ∀ l : ℝ, 0 < l → phi J p l x = θ ^ (1 / ((p : ℝ) - 1)) →
        GammaTheta J p θ x = (1 / l) ^ (1 / ((p : ℝ) - 1))) ∧
    (∀ x : H, x ∈ zer A → GammaTheta J p θ x = 0) ∧
    (∀ x₁ x₂ : H, |GammaTheta J p θ x₁ - GammaTheta J p θ x₂| ≤
      θ ^ (-(1 / ((p : ℝ) - 1))) * ‖x₁ - x₂‖) := by sorry

end MonoInclCLC
