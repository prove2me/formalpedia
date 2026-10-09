-- Prove2me | Theorems.Thm_NestedSA_NASA_lemma_3
-- name    : NestedSA.NASA.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:38:56.464994+00:00
-- url     : https://prove2.me/theorems/54fedf3a-b837-4069-807f-c97decf9678b
-- title:
--   Lemma 3 — the subproblem value η(x,z) has a Lipschitz gradient in (x,z)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be nonempty, closed and convex and $\beta>0$. Let
--   $$\eta(x,z)=\min_{y\in X}\Big\{\langle z,y-x\rangle+\frac\beta2\|y-x\|^2\Big\}$$
--   be the optimal value of subproblem (2.5), viewed as a function of the pair $(x,z)\in\mathbb R^n\times\mathbb R^n$ equipped with the Euclidean norm $\|(x,z)\|=\sqrt{\|x\|^2+\|z\|^2}$. Then $\eta$ is differentiable and its gradient is Lipschitz continuous with constant
--   $$L_{\nabla\eta}=2\sqrt{(1+\beta)^2+\Big(1+\frac1{2\beta}\Big)^2}.$$
--
--   The second term $-\eta(x,z)$ of the merit function $W$ is controlled through this smoothness bound.
--
--   **Formalization Note** The pair $(x,z)$ lives in the $L^2$ product `WithLp 2 (ℝⁿ × ℝⁿ)`, not in Mathlib's default product with the sup norm. The statement asserts differentiability and the Lipschitz bound only; it does not fix the formula of the gradient.
-- source:
--   Ghadimi, Ruszczyński, Wang, A Single Time-Scale Stochastic Approximation Method for Nested Stochastic Optimization, arXiv:1812.01094v2, p. 10, Lemma 3, (3.14)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic

namespace NestedSA.NASA

/-- Lemma 3 (p. 10): for a nonempty closed convex `X ⊆ ℝⁿ` with Euclidean projection `P` and `β > 0`, the optimal
value `η(x, z) = min_{y ∈ X} {⟨z, y − x⟩ + β/2 ‖y − x‖²}` of subproblem (2.5), viewed as a function of the joint
variable `(x, z)` with the Euclidean norm `√(‖x‖² + ‖z‖²)`, is differentiable and its gradient is Lipschitz
continuous with constant `L_∇η = 2 √((1 + β)² + (1 + 1/(2β))²)`. -/
theorem lemma_3 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (hX_ne : X.Nonempty) (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) (β : ℝ) (hβ : 0 < β) :
    Differentiable ℝ (etaJoint P β) ∧
      ∀ p q : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
        ‖gradient (etaJoint P β) p - gradient (etaJoint P β) q‖ ≤ Leta β * ‖p - q‖ := by sorry

end NestedSA.NASA
