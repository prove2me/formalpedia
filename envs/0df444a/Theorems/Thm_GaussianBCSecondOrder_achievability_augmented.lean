-- Prove2me | Theorems.Thm_GaussianBCSecondOrder_achievability_augmented
-- name    : GaussianBCSecondOrder.achievability_augmented
-- status  : Open
-- author  : @Vincent Tan
-- created : 2026-11-23T07:29:30.082066+00:00
-- url     : https://prove2.me/theorems/11e1350c-8b48-49de-9ec2-f9d515b0a3dd
-- title:
--   Proposition 5: second-order achievability with augmented error
-- statement:
--   This proposition is the achievability half of the main theorem, proved for the stronger augmented error criterion in which receiver 1 must decode both messages.
--
--   Let $S_1>S_2>0$, $\rho\in[-1,1]$ and $\varepsilon\in(0,1)$. A pair $(L_1,L_2)$ is achievable with augmented error at the first-order rate pair $R^*=(R_1^*,R_2^*)$ if there is a sequence of $(n,M_{1,n},M_{2,n})$-codes in which receiver 1 estimates both messages, with $\liminf_n(\log M_{j,n}-nR_j^*)/\sqrt n\ge L_j$ for $j=1,2$ and $\limsup_n e_n\le\varepsilon$, where $e_n$ is the augmented average error probability.
--
--   **Proposition.**
--
--   1. Let $0<\alpha<1$. Every $(L_1,L_2)$ such that, for some $\beta\in\mathbb R$,
--   $$\Psi_{\alpha,\rho}\Big(\frac{\beta S_1}{2(1+\alpha S_1)}-L_1,\,-\frac{\beta S_2}{2(1+\alpha S_2)}-L_2\Big)\ge1-\varepsilon$$
--   is achievable with augmented error at $R^*=(C_1(\alpha),C_2(\alpha))$.
--   2. Every $(L_1,L_2)$ with $L_1^++\frac{S_1}{S_2}L_2\le\frac{S_1}{S_2}\sqrt{\mathsf V(S_2)}\,\Phi^{-1}(\varepsilon)$ is achievable with augmented error at $R^*=(0,\mathsf C(S_2))$.
--   3. Every $(L_1,L_2)$ with $L_1+\frac{S_1(1+S_2)}{S_2(1+S_1)}L_2^+\le\sqrt{\mathsf V(S_1)}\,\Phi^{-1}(\varepsilon)$ is achievable with augmented error at $R^*=(\mathsf C(S_1),0)$.
--
--   Since $\varepsilon_{n,\mathrm{av}}\le e_n$, this gives achievability of the regions of Theorem 1 under the average error criterion; Lemma 6 then transfers it to maximal error.
--
--   **Formalization Note** The parameter assumptions $S_1>S_2>0$, $\rho\in[-1,1]$, $\varepsilon\in(0,1)$ of Theorem 1 are hypotheses. The $\liminf$ and $\limsup$ are taken in the extended reals.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, p. 12, Proposition 5, with eqs. (16), (28), (29), (33)

import Definitions.Def_GaussianBCSecondOrder_Superposition

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussianBCSecondOrder
theorem achievability_augmented (S₁ S₂ ρ ε : ℝ) (hS₂ : 0 < S₂) (hS : S₂ < S₁)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ L : ℝ × ℝ,
      (∃ β : ℝ, 1 - ε ≤
          Psi S₁ S₂ α ρ (β * S₁ / (2 * (1 + α * S₁)) - L.1)
            (-(β * S₂ / (2 * (1 + α * S₂))) - L.2)) →
        AugAchievable S₁ S₂ ρ ε (C₁ S₁ α, C₂ S₂ α) L) ∧
    (∀ L : ℝ × ℝ,
      max L.1 0 + S₁ / S₂ * L.2 ≤ S₁ / S₂ * Real.sqrt (dispersion S₂) * PhiInv ε →
        AugAchievable S₁ S₂ ρ ε (0, capacity S₂) L) ∧
    (∀ L : ℝ × ℝ,
      L.1 + S₁ * (1 + S₂) / (S₂ * (1 + S₁)) * max L.2 0 ≤
          Real.sqrt (dispersion S₁) * PhiInv ε →
        AugAchievable S₁ S₂ ρ ε (capacity S₁, 0) L) := by sorry
end GaussianBCSecondOrder
