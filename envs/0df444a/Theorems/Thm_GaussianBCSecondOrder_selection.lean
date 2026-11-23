-- Prove2me | Theorems.Thm_GaussianBCSecondOrder_selection
-- name    : GaussianBCSecondOrder.selection
-- status  : Open
-- author  : @Vincent Tan
-- created : 2026-11-23T07:33:49.070143+00:00
-- url     : https://prove2.me/theorems/ba6cdaf1-37b5-432c-9523-9c0fd437ad85
-- title:
--   Lemma 8: selection preserves success probability
-- statement:
--   This lemma is the first reduction step of the converse: from an arbitrary code it extracts one receiver-2 message and a large set of receiver-1 messages on which joint decoding still succeeds with high probability.
--
--   Let $S_1>S_2>0$, $\rho\in[-1,1]$ and $\alpha\in[0,1]$, and let $\mu_\alpha=\frac{S_1(1+\alpha S_2)}{S_2(1+\alpha S_1)}$ and $T=1+1/S_2$. Consider an $(n,M_{1,n},M_{2,n})$-code all of whose codewords satisfy $\|x^n(m_1,m_2)\|^2=n$, with decoding regions $\mathcal B_{m_2}=\varphi_{2,n}^{-1}(m_2)$ and joint success probabilities $s(m_1,m_2)$.
--
--   **Lemma.** Suppose the code has average probability of successful decoding at least $1-\varepsilon-\zeta/2$, where $\varepsilon,\zeta>0$ and $\varepsilon+\zeta<1$. Set $\theta=\zeta/[2(\varepsilon+\zeta)]$. Then there are a message index $k\in[M_{2,n}]$ and a nonempty set $\mathcal I\subset[M_{1,n}]$ such that, with $M=|\mathcal I|$, $\mathcal B=\mathcal B_k$ and $Q_0=\mathcal N(0,TI_n)$:
--
--   1. $s(m_1,k)\ge1-\varepsilon-\zeta$ for all $m_1\in\mathcal I$;
--   2. $M\ge\frac\theta2M_{1,n}$;
--   3. $0<q:=Q_0(\mathcal B)\le\dfrac2{\theta M_{2,n}}$;
--   4. $\dfrac1M\sum_{m_1\in\mathcal I}s(m_1,k)\ge1-\varepsilon-\zeta$;
--   5. $\Xi:=\log M-\mu_\alpha\log q\ \ge\ \log M_{1,n}+\mu_\alpha\log M_{2,n}-(1+\mu_\alpha)\log\dfrac2\theta$.
--
--   An upper bound on $\Xi$ therefore bounds the weighted sum $\log M_{1,n}+\mu_\alpha\log M_{2,n}$ up to a constant, which is negligible at the second-order scale.
--
--   **Formalization Note** The hypotheses $S_1>S_2>0$, $\rho\in[-1,1]$, $\alpha\in[0,1]$ and the equal-energy condition are the standing assumptions of Section IV-B of the paper (the latter after the reduction of Lemma 7) and are included as hypotheses. $Q_0$ is Mathlib's `multivariateGaussian 0 (T • 1)` on `EuclideanSpace ℝ (Fin n)`, and $\mathcal I$ is a `Finset`.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, p. 15, Lemma 8, eqs. (77)-(81), with the standing assumptions of Section IV-B

import Definitions.Def_GaussianBCSecondOrder_Codes

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussianBCSecondOrder
theorem selection (S₁ S₂ ρ α ε ζ : ℝ) (hS₂ : 0 < S₂) (hS : S₂ < S₁)
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hε : 0 < ε) (hζ : 0 < ζ) (hεζ : ε + ζ < 1)
    (n M₁ M₂ : ℕ) (code : Code n M₁ M₂)
    (henergy : ∀ m₁ m₂, ‖code.encoder m₁ m₂‖ ^ 2 = (n : ℝ))
    (hsucc : 1 - ε - ζ / 2 ≤ code.avgSuccess S₁ S₂ ρ) :
    ∃ (k : Fin M₂) (I : Finset (Fin M₁)), I.Nonempty ∧
      (∀ m₁ ∈ I, 1 - ε - ζ ≤ code.condSuccess S₁ S₂ ρ m₁ k) ∧
      ζ / (2 * (ε + ζ)) / 2 * M₁ ≤ (I.card : ℝ) ∧
      0 < (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            ((1 + 1 / S₂) • (1 : Matrix (Fin n) (Fin n) ℝ))).real (code.decoder₂ ⁻¹' {k}) ∧
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            ((1 + 1 / S₂) • (1 : Matrix (Fin n) (Fin n) ℝ))).real (code.decoder₂ ⁻¹' {k}) ≤
        2 / (ζ / (2 * (ε + ζ)) * M₂) ∧
      1 - ε - ζ ≤ (1 / (I.card : ℝ)) * ∑ m₁ ∈ I, code.condSuccess S₁ S₂ ρ m₁ k ∧
      Real.log M₁ + mu S₁ S₂ α * Real.log M₂ -
          (1 + mu S₁ S₂ α) * Real.log (2 / (ζ / (2 * (ε + ζ)))) ≤
        Real.log (I.card : ℝ) - mu S₁ S₂ α *
          Real.log ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            ((1 + 1 / S₂) • (1 : Matrix (Fin n) (Fin n) ℝ))).real (code.decoder₂ ⁻¹' {k})) := by sorry
end GaussianBCSecondOrder
