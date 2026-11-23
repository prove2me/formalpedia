-- Prove2me | Theorems.Thm_GaussianBCSecondOrder_finite_blocklength_bound
-- name    : GaussianBCSecondOrder.finite_blocklength_bound
-- status  : Open
-- author  : @Vincent Tan
-- created : 2026-11-23T07:28:10.016839+00:00
-- url     : https://prove2.me/theorems/c09fa2e1-b930-44ee-b8a6-2bc5e63744b5
-- title:
--   Lemma 3: finite blocklength upper bound for spherical superposition coding
-- statement:
--   This lemma is the non-asymptotic achievability bound from which the second-order achievability is derived.
--
--   Let $S_1>S_2>0$. For $\alpha\in(0,1)$ and deterministic $u^n,v^n\in\mathbb R^n$ with $\|u^n\|^2=n(1-\alpha)$, $\|v^n\|^2=n\alpha$, $\langle u^n,v^n\rangle=0$ (eq. (48)), let $\iota_0,\iota_1,\iota_2$ be the information densities of eq. (49), viewed as random variables in the correlated noise $(Z_1^n,Z_2^n)$ with $u^n,v^n$ held fixed. An augmented code is a code in which receiver 1 estimates both messages; its augmented average error probability $e_n$ is the average probability that any of the three estimates is wrong.
--
--   **Lemma.** There are constants $K\ge1$, $c>0$ and $n_0\ge3$, depending only on $S_1$ and $S_2$, such that for every $n\ge n_0$, $\alpha\in(0,1)$, $\rho\in[-1,1]$, positive integers $M_{1,n},M_{2,n}$ and $\gamma>0$ there is an $(n,M_{1,n},M_{2,n})$-code, all of whose codewords have energy exactly $n$, in which receiver 1 estimates both messages and receiver 2 estimates $W_2$, with
--   $$e_n\le 1-\Pr(\iota_1>t_1,\ \iota_2>t_2)+\Pr(\iota_0\le t_0)+3e^{-\gamma}+e^{-cn},$$
--   where $t_1=\log M_{1,n}+\log K+\gamma$ and $t_0=t_2=\log M_{2,n}+\log K+\gamma$.
--
--   The bound reduces the error analysis of superposition coding to the joint distribution of three information densities.
--
--   **Formalization Note** The standing assumption $S_1>S_2>0$ is a hypothesis. The probabilities on the right-hand side do not depend on the choice of the pair $(u^n,v^n)$; the Lean statement asserts the bound for every pair satisfying eq. (48). "Integers $M_{1,n},M_{2,n}$" is read as positive integers.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, p. 11, Lemma 3, eq. (50), with eqs. (48), (49)

import Definitions.Def_GaussianBCSecondOrder_Superposition

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussianBCSecondOrder
theorem finite_blocklength_bound (S₁ S₂ : ℝ) (hS₂ : 0 < S₂) (hS : S₂ < S₁) :
    ∃ (K c : ℝ) (n₀ : ℕ), 1 ≤ K ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      ∀ M₁ M₂ : ℕ, 0 < M₁ → 0 < M₂ → ∀ γ : ℝ, 0 < γ →
        ∃ code : AugCode n M₁ M₂,
          (∀ m₁ m₂, ‖code.encoder m₁ m₂‖ ^ 2 = (n : ℝ)) ∧
          ∀ u v : EuclideanSpace ℝ (Fin n), IsSuperpositionPair α u v →
            code.augAvgError S₁ S₂ ρ ≤
              1 - (noiseLaw S₁ S₂ ρ n).real
                    {z | Real.log M₁ + Real.log K + γ < info₁ S₁ α u v z ∧
                         Real.log M₂ + Real.log K + γ < info₂ S₂ α u v z}
                + (noiseLaw S₁ S₂ ρ n).real
                    {z | info₀ S₁ α u v z ≤ Real.log M₂ + Real.log K + γ}
                + 3 * Real.exp (-γ) + Real.exp (-(c * n)) := by sorry
end GaussianBCSecondOrder
