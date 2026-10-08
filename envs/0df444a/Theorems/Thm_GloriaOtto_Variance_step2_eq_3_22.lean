-- Prove2me | Theorems.Thm_GloriaOtto_Variance_step2_eq_3_22
-- name    : GloriaOtto.Variance.step2_eq_3_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:23.949016+00:00
-- url     : https://prove2.me/theorems/42f44814-8082-4a8e-a09f-4e50a0c628cb
-- title:
--   §3.2, proof of Theorem 2.1, Step 2, (3.22) — sup over a(e) of the derivative of the averaged energy density
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$. There is a constant $C$, depending only on $d, \alpha, \beta$, such that the following holds. Let $a \in \mathcal A_{\alpha\beta}$, $T > 0$, $\xi \in \mathbb R^d$ with $|\xi| = 1$, let $\eta_L$ satisfy (3.15) for some $L > 0$, and let $e = [z, z+e_i]$ be an edge. Then for every value $t \in [\alpha,\beta]$ of $a(e)$, the averaged energy density $\langle\langle T^{-1}\phi_T^2 + (\nabla\phi_T+\xi)\cdot A(\nabla\phi_T+\xi)\rangle\rangle_L$ is differentiable in $a(e)$ at $t$, and its derivative $D$ satisfies
--   $$|D| \le C\Big(\sum_x|\nabla_z G_T(z,x)|\,|\nabla^*\eta_L(x)|\big(|\nabla^*\phi_T(x)|^2 + |\nabla\phi_T(z)|^2 + 1\big) + \eta_L(z)\big(|\nabla\phi_T(z)|^2+1\big)\Big), \tag{3.22}$$
--   with every quantity on the right evaluated at the unperturbed $a$. Here $\nabla_z G_T(z,x) = (G_T(z+e_j,x) - G_T(z,x))_{j=1}^d$ is the full gradient in the first argument and all norms are Euclidean.
--
--   Combined with (3.16) (Lemmas 2.3 and 2.6), this reduces the variance of the averaged energy density to deterministic Green's-function bounds and moments of $\nabla\phi_T$.
--
--   **Formalization Note.** "$\sup_{a(e)}$" is rendered by quantifying over every value $t \in [\alpha,\beta]$, with the differentiability part of the conclusion. The constant does not depend on the mask.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, §3.2, proof of Theorem 2.1, Step 2, (3.22), p. 30

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem step2_eq_3_22 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ C : ℝ, ∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T → ∀ ξ : Fin d → ℝ, sqNorm ξ = 1 →
      ∀ (L Cη : ℝ) (η : Site d → ℝ), 0 < L → IsMask L Cη η →
      ∀ (z : Site d) (i : Fin d), ∀ t ∈ Set.Icc α β, ∃ D : ℝ,
        HasDerivAt (fun s => energyAvg (Function.update a (z, i) s) T ξ η) D t ∧
        |D| ≤ C * (∑' x, Real.sqrt (sqNorm (fun j => greenT a T (z + unit j) x - greenT a T z x))
                * Real.sqrt (sqNorm (gradStar η x))
                * (sqNorm (gradStar (phiT a T ξ) x) + sqNorm (grad (phiT a T ξ) z) + 1)
              + η z * (sqNorm (grad (phiT a T ξ) z) + 1)) := by sorry

end GloriaOtto.Variance
