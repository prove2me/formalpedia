-- Prove2me | Theorems.Thm_GaussianBCSecondOrder_gaussian_characterization
-- name    : GaussianBCSecondOrder.gaussian_characterization
-- status  : Open
-- author  : @Vincent Tan
-- created : 2026-11-23T07:27:47.20931+00:00
-- url     : https://prove2.me/theorems/f94f3e8b-6f43-4f9c-bbb6-e2f464681523
-- title:
--   Proposition 2: multivariate Gaussian characterization of $\mathsf{Q}_{\alpha,\rho}$ and $\mathsf{G}_{\alpha,\rho}$
-- statement:
--   This proposition establishes the properties of the dispersion matrix $\Sigma_\alpha(\rho)$, of the modified Q-function $\mathsf Q_{\alpha,\rho}$ and of its inverse $\mathsf G_{\alpha,\rho}$ that make the main theorem well posed, and gives equivalent forms of the second-order region.
--
--   Let $S_1>S_2>0$. For $(\mathsf Z_1,\mathsf Z_2)\sim\mathcal N(0,\Sigma_\alpha(\rho))$ let $\Psi_{\alpha,\rho}(z_1,z_2)=\Pr(\mathsf Z_1\le z_1,\mathsf Z_2\le z_2)$, $\mathsf Q_{\alpha,\rho}(r)=\sup_{z_1+\mu_\alpha z_2=r}\Pr(\mathsf Z_1\ge z_1,\mathsf Z_2\ge z_2)$ and $\mathsf G_{\alpha,\rho}(\varepsilon)=\mathsf Q_{\alpha,\rho}^{-1}(1-\varepsilon)$, with $\mu_\alpha$, $V_1$, $V_2$ as in the definitions file.
--
--   **Proposition.** Fix $\alpha\in[0,1]$ and $\rho\in[-1,1]$.
--
--   1. $\Sigma_\alpha(\rho)$ is positive semidefinite, and positive definite if $\alpha\in(0,1)$.
--   2. For every $r\in\mathbb R$ the supremum defining $\mathsf Q_{\alpha,\rho}(r)$ is attained.
--   3. $\mathsf Q_{\alpha,\rho}$ is continuous and strictly decreasing, with limits $1$ at $-\infty$ and $0$ at $+\infty$.
--   4. $\mathsf G_{\alpha,\rho}$ is continuous on $(0,1)$ and, for $\varepsilon\in(0,1)$,
--   $$\mathsf G_{\alpha,\rho}(\varepsilon)=\max_{(z_1,z_2):\ \Pr(\mathsf Z_1\ge z_1,\mathsf Z_2\ge z_2)\ge1-\varepsilon}\big(z_1+\mu_\alpha z_2\big).$$
--   5. At the power endpoints, for all $r\in\mathbb R$ and $\varepsilon\in(0,1)$,
--   $$\mathsf Q_{0,\rho}(r)=\Phi\Big(-\frac r{\mu_0\sqrt{V_2(0)}}\Big),\quad \mathsf Q_{1,\rho}(r)=\Phi\Big(-\frac r{\sqrt{V_1(1)}}\Big),\quad \mathsf G_{0,\rho}(\varepsilon)=\mu_0\sqrt{V_2(0)}\,\Phi^{-1}(\varepsilon),\quad \mathsf G_{1,\rho}(\varepsilon)=\sqrt{V_1(1)}\,\Phi^{-1}(\varepsilon).$$
--   6. For $0<\alpha<1$ and $\varepsilon\in(0,1)$,
--   $$\big\{(L_1,L_2):L_1+\mu_\alpha L_2\le\mathsf G_{\alpha,\rho}(\varepsilon)\big\}=\bigcup_{\beta\in\mathbb R}\Big\{(L_1,L_2):\Psi_{\alpha,\rho}\Big(\frac{\beta S_1}{2(1+\alpha S_1)}-L_1,\,-\frac{\beta S_2}{2(1+\alpha S_2)}-L_2\Big)\ge1-\varepsilon\Big\}.$$
--   7. For $0<\alpha<1$, $\rho=0$ and $\varepsilon\in(0,1)$,
--   $$\mathsf G_{\alpha,0}(\varepsilon)=\max_{e_1,e_2\in(0,1):\ (1-e_1)(1-e_2)\ge1-\varepsilon}\Big(\sqrt{V_1(\alpha)}\,\Phi^{-1}(e_1)+\mu_\alpha\sqrt{V_2(\alpha)}\,\Phi^{-1}(e_2)\Big).$$
--
--   The union over $\beta$ in item 6 corresponds to perturbing the power split as $\alpha_n=\alpha+\beta/\sqrt n$, and is the form in which achievability is proved.
--
--   **Formalization Note** The standing assumption $S_1>S_2>0$ of the paper is a hypothesis. Each "max" is stated as `IsGreatest` (the value is attained and is an upper bound); item 6 is stated as an equality of subsets of $\mathbb R^2$ between the halfspace of eq. (27) and the union of eq. (33).
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, p. 8, Proposition 2, eqs. (30)-(35)

import Definitions.Def_GaussianBCSecondOrder_Functions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussianBCSecondOrder
theorem gaussian_characterization (S₁ S₂ : ℝ) (hS₂ : 0 < S₂) (hS : S₂ < S₁)
    (α ρ : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (dispersionMatrix S₁ S₂ α ρ).PosSemidef ∧
    (α ∈ Set.Ioo (0 : ℝ) 1 → (dispersionMatrix S₁ S₂ α ρ).PosDef) ∧
    (∀ r : ℝ, ∃ z : ℝ × ℝ, z.1 + mu S₁ S₂ α * z.2 = r ∧
      upperTail S₁ S₂ α ρ z.1 z.2 = Qfun S₁ S₂ α ρ r) ∧
    Continuous (Qfun S₁ S₂ α ρ) ∧
    StrictAnti (Qfun S₁ S₂ α ρ) ∧
    Tendsto (Qfun S₁ S₂ α ρ) atBot (𝓝 1) ∧
    Tendsto (Qfun S₁ S₂ α ρ) atTop (𝓝 0) ∧
    ContinuousOn (Gfun S₁ S₂ α ρ) (Set.Ioo (0 : ℝ) 1) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      IsGreatest
        ((fun z : ℝ × ℝ => z.1 + mu S₁ S₂ α * z.2) ''
          {z | 1 - ε ≤ upperTail S₁ S₂ α ρ z.1 z.2})
        (Gfun S₁ S₂ α ρ ε)) ∧
    (∀ r : ℝ, Qfun S₁ S₂ 0 ρ r = Phi (-(r / (mu S₁ S₂ 0 * Real.sqrt (V₂ S₂ 0))))) ∧
    (∀ r : ℝ, Qfun S₁ S₂ 1 ρ r = Phi (-(r / Real.sqrt (V₁ S₁ 1)))) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      Gfun S₁ S₂ 0 ρ ε = mu S₁ S₂ 0 * Real.sqrt (V₂ S₂ 0) * PhiInv ε) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 1, Gfun S₁ S₂ 1 ρ ε = Real.sqrt (V₁ S₁ 1) * PhiInv ε) ∧
    (α ∈ Set.Ioo (0 : ℝ) 1 → ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      {L : ℝ × ℝ | L.1 + mu S₁ S₂ α * L.2 ≤ Gfun S₁ S₂ α ρ ε} =
        ⋃ β : ℝ, {L : ℝ × ℝ | 1 - ε ≤
          Psi S₁ S₂ α ρ (β * S₁ / (2 * (1 + α * S₁)) - L.1)
            (-(β * S₂ / (2 * (1 + α * S₂))) - L.2)}) ∧
    (α ∈ Set.Ioo (0 : ℝ) 1 → ρ = 0 → ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      IsGreatest
        ((fun e : ℝ × ℝ =>
            Real.sqrt (V₁ S₁ α) * PhiInv e.1 + mu S₁ S₂ α * Real.sqrt (V₂ S₂ α) * PhiInv e.2) ''
          {e | e.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ e.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
            1 - ε ≤ (1 - e.1) * (1 - e.2)})
        (Gfun S₁ S₂ α 0 ε)) := by sorry
end GaussianBCSecondOrder
