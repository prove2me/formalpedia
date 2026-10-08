-- Prove2me | Theorems.Thm_InertialAVD_StrongCvx_eq_27
-- name    : InertialAVD.StrongCvx.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:19.641254+00:00
-- url     : https://prove2.me/theorems/2c06bddc-9971-4df6-b312-69e1cbd87bbf
-- title:
--   (27) — for t ≥ t₁, Φ(x(t)) − min Φ ≤ 2E^p_λ(t₁)t^{−p−2} = [2E^{2(α−3)/3}_{2α/3}(t₁)] t^{−2α/3}
-- statement:
--   Under the hypotheses of (26) ($\Phi$ continuously differentiable and strongly convex with constant $\mu>0$, $\alpha>3$, $x$ a solution of $\ddot x+\frac\alpha t\dot x+\nabla\Phi(x)=0$ on $[t_0,+\infty[$ with $t_0>0$, $x^*\in\operatorname{argmin}\Phi$, $p=\frac23(\alpha-3)$, $\lambda=\frac23\alpha$, $t_1=\max\{t_0,\sqrt{p\lambda/\mu}\}$), for every $t\ge t_1$,
--   $$\Phi(x(t))-\min\Phi\le2\mathcal E^p_\lambda(t_1)\,t^{-p-2}=\Big[2\mathcal E^{\frac23(\alpha-3)}_{\frac23\alpha}(t_1)\Big]\,t^{-\frac23\alpha}.\tag{27}$$
--
--   This is the explicit form of the first rate in (25).
--
--   **Formalization Note** Both the inequality and the equality of the chain are stated; the equality is the substitution $p+2=\frac23\alpha$. $\min\Phi$ is written $\Phi(x^*)$; $t^{-p-2}$ and $t^{-2\alpha/3}$ are real powers of $t>0$.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 11, (27) (proof of Theorem 3.4)

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting

open InnerProductSpace Filter Topology Asymptotics

namespace InertialAVD.StrongCvx

theorem eq_27 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) :
    ∀ t, t1 t₀ α μ ≤ t →
      Φ (x t) - Φ xstar
          ≤ 2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2) ∧
      2 * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2)
          = 2 * energyP Φ x v xstar (2 / 3 * α) (2 / 3 * (α - 3)) (t1 t₀ α μ)
              * t ^ (-(2 / 3) * α) := by sorry

end InertialAVD.StrongCvx
