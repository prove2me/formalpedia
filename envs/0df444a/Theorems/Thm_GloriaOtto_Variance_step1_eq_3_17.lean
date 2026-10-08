-- Prove2me | Theorems.Thm_GloriaOtto_Variance_step1_eq_3_17
-- name    : GloriaOtto.Variance.step1_eq_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:42.790098+00:00
-- url     : https://prove2.me/theorems/c7d37700-7a67-437d-a583-f4c03bdb22e0
-- title:
--   §3.2, proof of Theorem 2.1, Step 1, (3.17) — the derivative of ⟨⟨T⁻¹φ_T² + (∇φ_T+ξ)·A(∇φ_T+ξ)⟩⟩_L with respect to a(e)
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$, $a \in \mathcal A_{\alpha\beta}$, $T > 0$, $\xi \in \mathbb R^d$ with $|\xi| = 1$, and let $\eta_L$ be a mask satisfying (3.15) for some $L > 0$. For an edge $e = [z, z+e_i]$, the averaged energy density
--   $$\langle\langle T^{-1}\phi_T^2 + (\nabla\phi_T+\xi)\cdot A(\nabla\phi_T+\xi)\rangle\rangle_L = \sum_x\Big(T^{-1}\phi_T(x)^2 + \big(\nabla\phi_T(x)+\xi\big)\cdot A(x)\big(\nabla\phi_T(x)+\xi\big)\Big)\eta_L(x)$$
--   is differentiable in $a(e)$, the other conductivities fixed, and
--   $$\frac{\partial}{\partial a(e)}\langle\langle\cdots\rangle\rangle_L = 2\sum_{x}\big(\nabla_i\phi_T(z)+\xi_i\big)\nabla_{z_i}G_T(z,x)\Big(\sum_{j=1}^d a(x-e_j,x)\nabla^*_j\eta_L(x)\big(\nabla^*_j\phi_T(x)+\xi_j\big)\Big) + \eta_L(z)\big(\nabla_i\phi_T(z)+\xi_i\big)^2,$$
--   where $\nabla_{z_i}G_T(z,x) = G_T(z+e_i,x) - G_T(z,x)$ and $\nabla^*_j\eta_L(x) = \eta_L(x) - \eta_L(x-e_j)$.
--
--   The derivative involves the gradient of the mask, which brings the extra factor $L^{-1}$ behind the optimal rate.
--
--   **Formalization Note.** $a(x-e_j,x)$ is the conductivity of the edge $(x-e_j, j)$. The sum over $x$ has finitely many nonzero terms because $\eta_L$ has finite support.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, §3.2, proof of Theorem 2.1, Step 1, (3.17), p. 28

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem step1_eq_3_17 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T → ∀ ξ : Fin d → ℝ, sqNorm ξ = 1 →
      ∀ (L Cη : ℝ) (η : Site d → ℝ), 0 < L → IsMask L Cη η →
      ∀ (z : Site d) (i : Fin d),
        HasDerivAt (fun t => energyAvg (Function.update a (z, i) t) T ξ η)
          (2 * ∑' x, (grad (phiT a T ξ) z i + ξ i) * (greenT a T (z + unit i) x - greenT a T z x)
              * ∑ j, a (x - unit j, j) * gradStar η x j * (gradStar (phiT a T ξ) x j + ξ j)
            + η z * (grad (phiT a T ξ) z i + ξ i) ^ 2)
          (a (z, i)) := by sorry

end GloriaOtto.Variance
