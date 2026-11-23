-- Prove2me | Theorems.Thm_GaussianBCSecondOrder_second_order_region
-- name    : GaussianBCSecondOrder.second_order_region
-- status  : Open
-- author  : @Vincent Tan
-- created : 2026-11-23T07:34:25.243355+00:00
-- url     : https://prove2.me/theorems/07671206-da2a-4bd3-b306-c2aa5db9037f
-- title:
--   Theorem 1: second-order coding region of the scalar Gaussian broadcast channel
-- statement:
--   This is the main theorem of the paper: an exact characterization of the second-order coding region of the scalar Gaussian broadcast channel at every point of the curved boundary of its capacity region.
--
--   Let $S_1>S_2>0$ be the signal-to-noise ratios of the two receivers and $\rho\in[-1,1]$ the noise correlation coefficient. The normalized channel is $Y_j^n=X^n+Z_j^n$, $j=1,2$, where the noise pairs $(Z_{1,i},Z_{2,i})$, $i=1,\dots,n$, are i.i.d. centered Gaussian with variances $1/S_1$, $1/S_2$ and covariance $\rho/\sqrt{S_1S_2}$, and codewords satisfy $\|x^n\|^2\le n$. An error occurs when either receiver fails to decode its own message. For $\varepsilon\in(0,1)$, a first-order rate pair $R^*$ and $\dagger\in\{\mathrm{av},\mathrm{max}\}$, the second-order region $\mathcal L_\dagger(\varepsilon;R^*)$ is the closure of the set of pairs $(L_1,L_2)\in\mathbb R^2$ for which there are $(n,M_{1,n},M_{2,n},\varepsilon_n)_\dagger$-codes with $\liminf_n(\log M_{j,n}-nR_j^*)/\sqrt n\ge L_j$, $j=1,2$, and $\limsup_n\varepsilon_n\le\varepsilon$.
--
--   Write $\mathsf C(x)=\tfrac12\log(1+x)$, $\mathsf V(x)=\frac{x(x+2)}{2(x+1)^2}$, $C_1(\alpha)=\mathsf C(\alpha S_1)$, $C_2(\alpha)=\mathsf C\big(\tfrac{(1-\alpha)S_2}{1+\alpha S_2}\big)$ and $\mu_\alpha=\frac{S_1(1+\alpha S_2)}{S_2(1+\alpha S_1)}$. Let $\mathsf G_{\alpha,\rho}(\varepsilon)=\mathsf Q_{\alpha,\rho}^{-1}(1-\varepsilon)$, where $\mathsf Q_{\alpha,\rho}(r)$ is the supremum of $\Pr(\mathsf Z_1\ge z_1,\mathsf Z_2\ge z_2)$ over $z_1+\mu_\alpha z_2=r$ for $(\mathsf Z_1,\mathsf Z_2)\sim\mathcal N(0,\Sigma_\alpha(\rho))$, and let $\Phi$ be the standard Gaussian distribution function.
--
--   **Theorem.** Let $S_1>S_2>0$, $\rho\in[-1,1]$ and $\varepsilon\in(0,1)$. The second-order regions under the average and maximal joint-error criteria coincide at every $R^*=(C_1(\alpha),C_2(\alpha))$, $\alpha\in[0,1]$. Denoting the common region by $\mathcal L(\varepsilon;R^*)$:
--
--   1. If $R^*=(C_1(\alpha),C_2(\alpha))$ with $0<\alpha<1$, then
--   $$\mathcal L(\varepsilon;R^*)=\big\{(L_1,L_2)\in\mathbb R^2:\ L_1+\mu_\alpha L_2\le \mathsf G_{\alpha,\rho}(\varepsilon)\big\}.$$
--   2. If $R^*=(0,\mathsf C(S_2))$, then
--   $$\mathcal L(\varepsilon;R^*)=\Big\{(L_1,L_2)\in\mathbb R^2:\ L_1^+ +\frac{S_1}{S_2}L_2\le\frac{S_1}{S_2}\sqrt{\mathsf V(S_2)}\,\Phi^{-1}(\varepsilon)\Big\}.$$
--   3. If $R^*=(\mathsf C(S_1),0)$, then
--   $$\mathcal L(\varepsilon;R^*)=\Big\{(L_1,L_2)\in\mathbb R^2:\ L_1+\frac{S_1(1+S_2)}{S_2(1+S_1)}L_2^+\le\sqrt{\mathsf V(S_1)}\,\Phi^{-1}(\varepsilon)\Big\}.$$
--
--   Here $x^+=\max\{x,0\}$. The theorem identifies the exact $n^{-1/2}$-scale backoff from the capacity boundary at a fixed non-vanishing error probability, including its dependence on the noise correlation.
--
--   **Formalization Note** The Lean statement is a conjunction of four clauses: the coincidence of the two regions for all $\alpha\in[0,1]$, and the three formulas, each asserted for both error criteria. The definitions of codes, of the region (closure of achievable pairs, with $\liminf$/$\limsup$ in the extended reals) and of $\mathsf G_{\alpha,\rho}$, $\Phi^{-1}$ are those of the imported definition files.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, p. 7, Theorem 1, eqs. (27)-(29)

import Definitions.Def_GaussianBCSecondOrder_Codes

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussianBCSecondOrder
theorem second_order_region (S₁ S₂ ρ ε : ℝ) (hS₂ : 0 < S₂) (hS : S₂ < S₁)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ α ∈ Set.Icc (0 : ℝ) 1,
      secondOrderRegion .avg S₁ S₂ ρ ε (C₁ S₁ α, C₂ S₂ α) =
        secondOrderRegion .max S₁ S₂ ρ ε (C₁ S₁ α, C₂ S₂ α)) ∧
    (∀ crit : Criterion, ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      secondOrderRegion crit S₁ S₂ ρ ε (C₁ S₁ α, C₂ S₂ α) =
        {L : ℝ × ℝ | L.1 + mu S₁ S₂ α * L.2 ≤ Gfun S₁ S₂ α ρ ε}) ∧
    (∀ crit : Criterion,
      secondOrderRegion crit S₁ S₂ ρ ε (0, capacity S₂) =
        {L : ℝ × ℝ | max L.1 0 + S₁ / S₂ * L.2 ≤
          S₁ / S₂ * Real.sqrt (dispersion S₂) * PhiInv ε}) ∧
    (∀ crit : Criterion,
      secondOrderRegion crit S₁ S₂ ρ ε (capacity S₁, 0) =
        {L : ℝ × ℝ | L.1 + S₁ * (1 + S₂) / (S₂ * (1 + S₁)) * max L.2 0 ≤
          Real.sqrt (dispersion S₁) * PhiInv ε}) := by sorry
end GaussianBCSecondOrder
